with import <nixpkgs> {};
stdenv.mkDerivation {
  name = "van-tonder";
  buildInputs = [
    dotnet-sdk
  ];
}
