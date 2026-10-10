import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreIntegralReplacementFrameWeighted
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregationSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationBiasedKernelSumSymbolic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedBulkErrorBudget

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPatternIntegralReplacement
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkSourceDisintegration HistoryPairSourceLaws HistoryPairRepresentatives
open HistoryPairKernelReplacement HistoryBulkFibreGiantApproximation
open HistoryBulkFibreIntegralReplacementFrame HistoryBulkGoodPatternPrincipalFrame
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance bulkPatternInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

structure Reference {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ) (l : ℕ)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) where
  frame : Frame (l:=l) C outside
  nonbulk : SelectedNonbulkSample C l
  permutation : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))
  representative : Block p ≃ Representative frame.left frame.right
  mask : ℝ
  mask_mem : 0 ≤ mask  ∧  mask ≤ 1

variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}

def Reference.weight (r : Reference C outside l p)
    (b : Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (mixed : Bool) : ℂ :=
  ((r.mask*∏q:Block p,symbolicKernel mixed r.frame.left r.frame.right
    r.frame.left_supported r.frame.right_supported (r.representative q) (b q).val : ℝ):ℂ)

theorem Reference.weight_norm_le (r : Reference C outside l p)
    (b : Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (mixed : Bool) : ‖r.weight b mixed‖ ≤ ∏q:Block p,2/((b q).val:ℝ) := by
  have hK (q : Block p) := symbolicKernel_le_two_div mixed r.frame.left r.frame.right
    r.frame.left_supported r.frame.right_supported (r.representative q) (b q).val
    (commonSample_prime C.sources _ (b q))
  have hn : 0 ≤ ∏q:Block p,symbolicKernel mixed r.frame.left r.frame.right
      r.frame.left_supported r.frame.right_supported (r.representative q) (b q).val :=
    Finset.prod_nonneg (fun q _=>(hK q).1)
  rw [Reference.weight,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg r.mask_mem.1 hn)]
  exact (mul_le_of_le_one_left hn r.mask_mem.2).trans
    (Finset.prod_le_prod₀ (fun q _=>(hK q).1) (fun q _=>(hK q).2))

abbrev Family (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ) (l : ℕ)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) :=
  FrequencyChoices (frequencyBound Bs BD Bz k L) (l+1) → Option (Reference C outside l p)

def familyValue (after : Bool) (F : Family C outside l p)
    (b : Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (corrected mixed : Bool)
    (hV : ∀q∈outside,∀j ≤ l,frequencyBound Bs BD Bz k L j<q) : ℂ :=
  ∑i,(F i).elim 0 (fun r=>r.weight b mixed *
    (rootDensity r.frame mixed * (if after then
      principalOperator r.frame corrected mixed r.permutation hV else
      bulkMean r.frame corrected mixed r.nonbulk r.permutation hV)))

theorem familyValue_sub_norm_le (F : Family C outside l p)
    (b : Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (corrected mixed : Bool)
    (hV : ∀q∈outside,∀j ≤ l,frequencyBound Bs BD Bz k L j<q)
    (ε : ℝ) (hε : 0 ≤ ε)
    (herr : ∀i r,F i=some r  → 
      ‖rootDensity r.frame mixed*bulkMean r.frame corrected mixed r.nonbulk r.permutation hV-
        rootDensity r.frame mixed*principalOperator r.frame corrected mixed r.permutation hV‖ ≤ ε) :
    ‖familyValue false F b corrected mixed hV-familyValue true F b corrected mixed hV‖ ≤ 
      ((Fintype.card (FrequencyChoices (frequencyBound Bs BD Bz k L) (l+1)):ℝ)*ε)*
        ∏q:Block p,2/((b q).val:ℝ) := by
  classical
  unfold familyValue
  rw [←Finset.sum_sub_distrib]
  calc
    _  ≤  ∑i,‖(F i).elim 0 (fun r=>r.weight b mixed*(rootDensity r.frame mixed*
        (if false then principalOperator r.frame corrected mixed r.permutation hV else
          bulkMean r.frame corrected mixed r.nonbulk r.permutation hV)))-
      (F i).elim 0 (fun r=>r.weight b mixed*(rootDensity r.frame mixed*
        (if true then principalOperator r.frame corrected mixed r.permutation hV else
          bulkMean r.frame corrected mixed r.nonbulk r.permutation hV)))‖ := norm_sum_le _ _
    _  ≤  ∑_i:FrequencyChoices (frequencyBound Bs BD Bz k L) (l+1),
        ε*(∏q:Block p,2/((b q).val:ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      cases hi : F i with
      | none => simp only [Option.elim_none,sub_self,norm_zero]; positivity
      | some r =>
        simp only [Option.elim_some,Bool.false_eq_true,ite_false,ite_true]
        rw [←mul_sub,norm_mul]
        simpa only [mul_comm] using mul_le_mul (r.weight_norm_le b mixed)
          (herr i r hi) (norm_nonneg _) (by positivity : 0 ≤ ∏q:Block p,2/((b q).val:ℝ))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end Ostmann.Arithmetic.HistoryBulkPatternIntegralReplacement

end

end OAI
