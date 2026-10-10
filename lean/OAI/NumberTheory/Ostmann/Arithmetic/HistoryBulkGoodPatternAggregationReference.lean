import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGoodPatternAggregationBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationBiasedKernelSumSymbolic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkGoodPatternAggregation
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairRepresentatives HistoryPairKernelReplacement
open HistoryBulkFibreGiantApproximation
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance goodPatternInternalDecidable (template : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal template l) := Classical.decEq _

structure Reference {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ) (l : ℕ)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) where
  frame : Frame (l:=l) C outside
  permutation : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2)))
  good : ¬TransferBadArrangement permutation
  representative : Block p ≃ Representative frame.left frame.right
  mask : ℝ
  mask_mem : 0 ≤ mask ∧ mask ≤ 1

variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
    {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}
    {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}

def Reference.weight (r : Reference C outside l p)
    (b : Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (mixed : Bool) : ℂ :=
  ((r.mask * ∏q:Block p,symbolicKernel mixed r.frame.left r.frame.right
    r.frame.left_supported r.frame.right_supported (r.representative q) (b q).val:ℝ):ℂ)

theorem Reference.weight_norm_le (r : Reference C outside l p)
    (b : Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (mixed : Bool) : ‖r.weight b mixed‖≤∏q:Block p,2/((b q).val:ℝ) := by
  have hK (q : Block p) := symbolicKernel_le_two_div mixed r.frame.left r.frame.right
    r.frame.left_supported r.frame.right_supported (r.representative q) (b q).val
    (commonSample_prime C.sources _ (b q))
  have hn : 0≤∏q:Block p,symbolicKernel mixed r.frame.left r.frame.right
      r.frame.left_supported r.frame.right_supported (r.representative q) (b q).val :=
    Finset.prod_nonneg (fun q _=>(hK q).1)
  rw [Reference.weight,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg r.mask_mem.1 hn)]
  exact (mul_le_of_le_one_left hn r.mask_mem.2).trans
    (Finset.prod_le_prod₀ (fun q _=>(hK q).1) (fun q _=>(hK q).2))

abbrev Family (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ) (l : ℕ)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) :=
  FrequencyChoices (frequencyBound Bs BD Bz k L) (l+1) → Option (Reference C outside l p)

end Ostmann.Arithmetic.HistoryBulkGoodPatternAggregation

end

end OAI
