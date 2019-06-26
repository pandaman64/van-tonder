// Learn more about F# at http://fsharp.org

open System
open System.Numerics

let inline dispose (disp: #System.IDisposable) =
    match disp with null -> () | x -> x.Dispose()

type ResultBuilder() =
    member inline this.Bind(m, f) = Result.bind f m
    member inline this.Return x = Ok x
    member inline this.ReturnFrom (x: Result<_, _>) = x
    member inline this.Delay f = f : unit -> _
    member inline this.Undelay f = f()
    member inline this.Run f = f()
    member inline this.TryWith (f, h) = try f() with exn -> h exn
    member inline this.TryFinally (f, h) = try f() finally h()
    member inline this.Using (disp: #System.IDisposable, m) =
      this.TryFinally(
        this.Delay(fun () -> m disp),
        fun () -> dispose disp
      )
    member inline this.Combine (a, b) = this.Bind (a, fun () -> b ())
    member inline this.Zero () = this.Return ()
    member inline this.While (cond, body: unit -> _) =
      let rec loop cond m =
        if cond () then this.Combine(this.Undelay m, fun () -> loop cond m)
        else this.Zero ()
      loop cond body
    member inline this.Yield x = this.Return x
    member inline this.For (xs: #seq<_>, exec) =
      this.Using(
        (xs :> seq<_>).GetEnumerator(),
        fun en ->
          this.While(
            en.MoveNext,
            this.Delay(fun () -> exec en.Current))
      )
let result = ResultBuilder()

type Const = 
    | Zero
    | One
    | H
    | X
    | Y
    | Z
    | Cnot

type Occurence =
    | Linear
    | NonLinear

[<StructuredFormatDisplay("{AsString}")>]
type Term = 
    | Var of string
    | Lam of string * Term
    | App of Term * Term
    | Const of Const
    | Suspension of Term
    | NonLinearLam of string * Term
    // Extension from van Tonder's calculus
    | Nil
    | Cons of Term * Term
with
    member this.AsString =
        match this with
        | Var x -> sprintf "%s" x
        | Lam (x, t) -> sprintf "(λ%s. %A)" x t
        | App (f, x) -> sprintf "(%A %A)" f x
        | Const c -> sprintf "%A" c
        | Suspension t -> sprintf "!%A" t
        | NonLinearLam (x, t) -> sprintf "(λ!%s. %A)" x t
        | Nil -> "nil"
        | Cons (t1, t2) -> sprintf "%A::%A" t1 t2
    member this.IsValue =
        match this with
        | Var _ | Const _ | Lam _ | NonLinearLam _ | Suspension _ | Nil -> true
        | Cons (t1, t2) -> t1.IsValue && t2.IsValue
        | _ -> false
    member this.FreeVariable =
        match this with
        | Var x -> Set.singleton x
        | Lam (x, t) | NonLinearLam (x, t) -> t.FreeVariable - Set.singleton x
        | App (t1, t2) | Cons (t1, t2) -> t1.FreeVariable + t2.FreeVariable
        | Const _ | Nil -> Set.empty
        | Suspension t -> t.FreeVariable
    member this.Occurence =
        match this with
        | Const _ | Nil -> Ok Map.empty
        | Var x -> Map.add x Linear Map.empty |> Ok
        | Lam (x, t) -> result {
                let! occurence = t.Occurence
                return! match Map.tryFind x occurence with
                        | Some Linear -> Map.remove x occurence |> Ok
                        | Some NonLinear -> sprintf "nonlinear use of %s in %A" x t |> Error
                        | None -> sprintf "no use of %s in %A" x t |> Error
            }
        | NonLinearLam (x, t) ->
            t.Occurence
            |> Result.map (Map.remove x)
        | App (t1, t2) | Cons (t1, t2) -> result {
                let! o1 = t1.Occurence
                let! o2 = t2.Occurence

                return! o1
                        |> Map.fold (fun s k v -> result {
                            let! s = s
                            return match (Map.tryFind k s, v) with
                                   | None, v -> Map.add k v s
                                   | Some _, _ -> Map.add k NonLinear s
                        }) (Ok o2)
            }
        | Suspension t -> result {
                let! o = t.Occurence
                return o |> Map.map (fun _ _ -> NonLinear)
            }
    member this.WellFormed =
        match this.Occurence with
        | Ok m when Map.isEmpty m -> true
        | _ -> false
    member this.Substitute x t =
        match this with
        | Const _ | Nil -> this
        | Var y when x = y -> t
        | Var _ -> this
        | Lam (y, _) when x = y -> failwith "name conflict"
        | Lam (y, t') -> Lam (y, t'.Substitute x t)
        | App (t1, t2) -> App (t1.Substitute x t, t2.Substitute x t)
        | Cons (t1, t2) -> Cons (t1.Substitute x t, t2.Substitute x t)
        | NonLinearLam (y, _) when x = y -> failwith "name conflict"
        | NonLinearLam (y, t') -> NonLinearLam (y, t'.Substitute x t)
        | Suspension t' -> t'.Substitute x t |> Suspension

[<StructuredFormatDisplay("{AsString}")>]
type Erased =
    | EPH
    | EVar of string
    | ELam of Erased
    | EApp of Erased * Erased
    | ESuspension of Erased
    | ECons of Erased * Erased
with
    member this.AsString =
        match this with
        | EPH -> "_"
        | EVar x -> x
        | ELam e -> sprintf "(_.%A)" e
        | EApp (t1, t2) -> sprintf "(%A %A)" t1 t2
        | ESuspension t -> sprintf "!%A" t
        | ECons (t1, t2) -> sprintf "%A::%A" t1 t2
    member this.Lookup x t =
        match this, t with
        | EVar y, _ when x = y -> t |> Some
        | ELam e, Lam (_, t)
        | ELam e, NonLinearLam (_, t)
        | ESuspension e, Suspension t -> e.Lookup x t
        | EApp (e1, e2), App (t1, t2)
        | ECons (e1, e2), Cons (t1, t2) -> 
            e1.Lookup x t1
            |> Option.orElseWith (fun () -> e2.Lookup x t2)
        | _ -> None      

let rec erase x t =
    match t with
    | Const _ | Nil -> EPH
    | Var x' when x = x' -> EPH
    | Var x -> EVar x
    | Lam (y, _) when x = y -> failwith "name conflict"
    | Lam (_, t) -> erase x t |> ELam
    | App (t1, t2) -> EApp (erase x t1, erase x t2)
    | Cons (t1, t2) -> ECons (erase x t1, erase x t2)
    | NonLinearLam (y, _) when x = y -> failwith "name conflict"
    | NonLinearLam (_, t) -> erase x t |> ELam
    | Suspension t -> erase x t |> ESuspension

    
[<StructuredFormatDisplay("{AsString}")>]
type History = 
    | HLApp of History
    | HRApp of History
    | HLam of (string * Erased)
    | HNonLinearLam of (string * Erased)
    | HNonLinearLamDiscard of (string * Term)
    | HGate of Const
    | HPH
    | HLCons of History
    | HRCons of History
with
    member this.AsString =
        match this with
        | HLApp h -> sprintf "(%A _)" h
        | HRApp h -> sprintf "(_ %A)" h
        | HLam (x, h) -> sprintf "((λ%s.%A) _)" x h
        | HNonLinearLam (x, h) -> sprintf "((λ!%s.%A) _)" x h
        | HNonLinearLamDiscard (x, t) -> sprintf "((λ!%s._) !%A)" x t
        | HGate g -> sprintf ("(%A _)") g
        | HPH -> "_"
        | HLCons h -> sprintf "%A::_" h
        | HRCons h -> sprintf "_::%A" h

let ZERO = Complex(0.0, 0.0)
let ONE = Complex(1.0, 0.0)
let I = Complex(0.0, 1.0)
let SQRT2 = Complex(sqrt 2.0, 0.0)

[<StructuredFormatDisplay("{AsString}")>]
type State = State of Map<History list * Term, Complex>
with
    member this.AsString =
        let threshold = 0.001
        let encode history =
            history
            |> List.map (sprintf "%A; ")
            |> List.fold (+) ""
        let (State s) = this
        s
        |> Map.toList
        |> List.filter (fun (_, p) -> p.Magnitude > threshold)
        |> List.map (fun ((history, t), p) -> sprintf "(%.2f + %.2fi)|%s%A>" p.Real p.Imaginary (encode history) t)
        |> String.concat " + "
    // TODO: consider global phase    
    member this.Equivalent other =
        let (State this) = this
        let (State other) = other
        this
        |> Map.forall (fun ht p -> 
            match Map.tryFind ht other with
            | Some q -> p = q
            | None when p = ZERO -> true
            | None -> false
        )

let initial t = Map.empty |> Map.add ([], t) ONE |> State

let rec stepTerm t =
    match t with
    | App (Lam (x, t), v) when v.IsValue ->
        [ONE, HLam (x, erase x t), t.Substitute x v]
    | App (NonLinearLam (x, t), v) when v.IsValue ->
        if t.FreeVariable |> Set.contains x then
            [ONE, HNonLinearLam (x, erase x t), t.Substitute x v]
        else
            [ONE, HNonLinearLamDiscard (x, v), t]
    | App (Const g, Const c) -> 
        let h = HGate g
        match g, c with
        | X, Zero -> [ONE, h, Const One]
        | X, One -> [ONE, h, Const Zero]
        | Y, Zero -> [-I, h, Const One]
        | Y, One -> [I, h, Const Zero]
        | Z, Zero -> [ONE, h, Const Zero]
        | Z, One -> [-ONE, h, Const One]
        | H, Zero -> [ONE / SQRT2, h, Const Zero; ONE / SQRT2, h, Const One]
        | H, One -> [ONE / SQRT2, h, Const Zero; -ONE / SQRT2, h, Const One]
        | _ -> failwith "invalid operation"
    | App (Const Cnot, Cons (Const c, Const t)) ->
        let h = HGate Cnot
        match c, t with
        | Zero, Zero -> [ONE, h, Cons (Const Zero, Const Zero)]
        | Zero, One -> [ONE, h, Cons (Const Zero, Const One)]
        | One, Zero -> [ONE, h, Cons (Const One, Const One)]
        | One, One -> [ONE, h, Cons (Const One, Const Zero)]
        | _ -> failwith "invalid operation"
    | App (t1, t2) when not t1.IsValue -> 
        stepTerm t1
        |> List.map (fun (p, h1, t1) -> (p, HLApp h1, App (t1, t2)))
    | App (v1, t2) ->
        stepTerm t2
        |> List.map (fun (p, h2, t2) -> (p, HRApp h2, App (v1, t2)))
    | Cons (t1, t2) when not t1.IsValue ->
        stepTerm t1
        |> List.map (fun (p, h1, t1) -> (p, HLCons h1, Cons (t1, t2)))
    | Cons (v1, t2) when not t2.IsValue ->
        stepTerm t2
        |> List.map (fun (p, h2, t2) -> (p, HRCons h2, Cons (v1, t2)))
    | _ -> [(ONE, HPH, t)]

let step s =
    let (State ss) = s
    ss
    |> Map.toList
    |> List.collect (fun ((hs, t), p) -> 
        stepTerm t
        |> List.map (fun (q, h, t) -> (p * q, h :: hs, t))
    )
    |> List.fold (fun m (p, hs, t) -> 
        match Map.tryFind (hs, t) m with
        | Some q -> Map.add (hs, t) (p + q) m
        | None -> Map.add (hs, t) p m
    ) Map.empty
    |> State

let invStep hs t = failwith "TODO: implement"

[<EntryPoint>]
let main argv =
    //let t = (App ((Lam ("x", Var "x")), Const Zero))
    let t = (App (Const H, (App (Const H, Const Zero))))
    //let t = (App (Const Cnot, (Cons (App (Const H, Const Zero), Const Zero))))
    let s = initial t
    printfn "%A" s
    let s = step s
    printfn "%A" s
    let s = step s
    printfn "%A" s
    let s = step s
    printfn "%A" s
    let s = step s
    printfn "%A" s
    0 // return an integer exit code
