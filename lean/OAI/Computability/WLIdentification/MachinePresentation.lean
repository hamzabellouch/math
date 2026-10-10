import OAI.Computability.WLIdentification.SeedLetter

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MachineRealizer
open Machine
variable (M : Machine) (d : Word → ℕ) (dp : NatPoly (fun X : Fin 1 → Word => d (X 0)))
    (hsize : ∀ w,inputSpan w<2^d w)
noncomputable abbrev pointP := CellularRealizer.pointP M.Letter
noncomputable abbrev edgeP := CellularRealizer.edgeP M.Letter d dp
noncomputable abbrev seedP := InitialRealizer.seedP d dp
abbrev TestLetter := {a : M.Letter // a.2=some 1}
noncomputable abbrev testP := Presented.fixed (TestLetter M)

noncomputable def circuit : CircuitRealizer (pointP M) (edgeP M d dp) (seedP d dp) (testP M)
    (fun w => d w+d w) (NatPoly.add dp dp) (fun w => M.compiledCircuit (d w) w) where
  pointIndex := CellularRealizer.pointIndex M.Letter
  edgeIndex := CellularRealizer.edgeIndex M.Letter d dp
  seedIndex := (Number.code (seedP d dp)).congr (by intro w x; rfl)
  testIndex := Number.fixed _ (fun x : TestLetter M => NaturalCode.fixed M.Letter x.val)
  dimension := CellularRealizer.dimension M.Letter
  source := CellularRealizer.source M.Letter d dp
  target := CellularRealizer.target M.Letter d dp M.localRule
  port := CellularRealizer.port M.Letter d dp M.localRule
  seedType := InitialRealizer.seedLetter M d dp hsize (fun a => NaturalCode.fixed (CellularCircuit.Gate M.Letter) (.scalar a))
  testType := Number.fixed _ (fun x : TestLetter M => NaturalCode.fixed (CellularCircuit.Gate M.Letter) (.scalar x.val))
  edgeDomain := (CellularRealizer.edgeMap M.Letter d dp).domain
  seedDomain := ((ProductRealizer.singletonConstant (seedP d dp) d dp false false).concat (InitialRealizer.seedMap d dp)).domain
  testDomain := ((ProductRealizer.singletonConstant (testP M) d dp true true).concat (ProductRealizer.identity (testP M) d dp)).domain
  edgeMapping := (CellularRealizer.edgeMap M.Letter d dp).mapping
end MachineRealizer
end FinitePresentation

end WLIdentification

end OAI
