import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalReplacement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkSourceDisintegration HistoryBulkReferenceFrequencyFamily
open HistoryBulkSelectedUniversalOperator HistoryBulkSelectedUniversalSymbolicFamily
open HistoryBulkFibreGiantApproximation HistoryBulkFibreIntegralReplacementFrame
open HistoryBulkGoodPatternPrincipalFrame HistoryBulkUniversalPatternAggregation
local instance actualUniversalPrincipalPointComposeInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
    {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}
    {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}

theorem symbolic_term_eq_frame_of_equalities
    (F : SymbolicPatternFamily C outside l p)
    (hp : ∀q∈outside,q.Prime) (i : RootPresent F.refs)
    (hσ : F.permutation=Equiv.refl _)
    (mixed : Bool) (hm : F.mask i=assignmentDensity (F.data i).assignment mixed)
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
    (f : Frame (l:=l) C outside) (κ : ℂ)
    (hf : frameOfData (F.data i) hp=f)
    (hw : (replacementReference F hp i).weight b mixed=κ) :
    symbolicFamilyWeight F.refs b F.representative mixed F.mask i *
        actualNestedIntegral C mixed (bulkSize k L/2) (F.data i) *
        referenceRootAverage mixed d k (2*(bulkSize k L/2)) F.permutation hp hV
          (rootSelected F.refs i)=
      rootDensity f mixed * κ * principalOperator f false mixed (Equiv.refl _) hV :=
  let hf' := (replacementReference_frame F hp i).trans hf
  let hd := congrArg (fun t=>rootDensity t mixed) hf'
  let ho := (congrArg (fun σ=>principalOperator (replacementReference F hp i).frame
      false mixed σ hV) ((replacementReference_permutation F hp i).trans hσ)).trans
    (congrArg (fun t=>principalOperator t false mixed (Equiv.refl _) hV) hf')
  (replacementReference_term F hp i hσ mixed hm b hV).symm.trans
    ((congrArg₂ (fun x y : ℂ=>x*y) hw
      (congrArg₂ (fun x y : ℂ=>x*y) hd ho)).trans
        ((mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm))

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
