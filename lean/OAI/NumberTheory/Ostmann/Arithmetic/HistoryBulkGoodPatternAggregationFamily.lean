import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGoodPatternAggregationReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGoodPatternPrincipalFrameDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkGoodPatternAggregation
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryBulkGoodPatternPrincipalFrame
open HistoryBulkSelectedGoodOperator
open scoped BigOperators
local instance goodFamilyInternalDecidable (template : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal template l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
    {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}
    {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}

def familyValue (F : Family C outside l p)
    (b : Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (corrected mixed : Bool)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) : ℂ :=
  ∑i,(F i).elim 0 (fun r=>r.weight b mixed *
    principalOperator r.frame corrected mixed r.permutation hV)

theorem familyValue_norm_le_of_paid (F : Family C outside l p)
    (b : Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (corrected mixed : Bool)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
    (T : ℝ) (hT : 0 ≤ T)
    (hpaid : ∀i r,F i=some r →
      principalPayment Bs BD Bz L k l *
        ‖principalOperator r.frame corrected mixed r.permutation hV‖ ≤ T) :
    ‖familyValue F b corrected mixed hV‖ ≤
      (T/Real.exp (2*(2:ℝ)^l*(bulkSize k L:ℝ))) *
        ∏q:Block p,2/((b q).val:ℝ) := by
  let W := fun i=>(F i).elim 0 (fun r=>r.weight b mixed)
  let J := fun i=>(F i).elim 0 (fun r=>principalOperator r.frame corrected mixed r.permutation hV)
  have hvalue : familyValue F b corrected mixed hV=∑i,W i*J i := by
    apply Finset.sum_congr rfl
    intro i _
    cases he : F i <;> simp only [W,J,he,Option.elim_none,Option.elim_some,zero_mul]
  rw [hvalue]
  apply norm_sum_mul_le_of_paid W J _ _ T (Real.exp_pos _)
    (Finset.prod_nonneg (fun q _=>div_nonneg (by norm_num) (Nat.cast_nonneg _))) hT
  · intro i
    cases he : F i with
    | none => simp only [W,he,Option.elim_none,norm_zero]; positivity
    | some r => simpa only [W,he,Option.elim_some] using r.weight_norm_le b mixed
  · intro i
    cases he : F i with
    | none => simpa only [J,he,Option.elim_none,norm_zero,mul_zero] using hT
    | some r =>
      simpa only [J,he,Option.elim_some,principalPayment] using hpaid i r he

end Ostmann.Arithmetic.HistoryBulkGoodPatternAggregation

end

end OAI
