import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairedFrequencyAverageCanonical
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairedFrequencyAverageHistory

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairedFrequencyAverage
open Construction Conclusion Characters FrequencyTreeSum HistoryFrequencyResidues
open PairedFrequencyActualBudget

theorem canonical_bulk_average_le_weight {ε : ℝ} {C : NNReal}
    (hcount : LeafCountConstant ε C) (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    (K : ℕ) {l : ℕ} (h h' : History l) {outside : List ℕ}
    (hs : h.Supported (frequencyBound Bs BD Bz k L) outside)
    (hs' : h'.Supported (frequencyBound Bs BD Bz k L) outside)
    (m : ℕ) (hm : 0 < m) :
    canonicalUnitBulkAverage K h h' hs hs' m ≤
      weight (pairedRanges Bs BD Bz k L l) (PairedFrequencyTreeSum.factor (C:ℝ) ε)
        (supportedHistoryAssignment Bs BD Bz k L h h' hs hs') ∧
    canonicalMixedBulkAverage K h h' hs hs' m ≤
      weight (pairedRanges Bs BD Bz k L l) (PairedFrequencyTreeSum.factor (C:ℝ) ε)
        (supportedHistoryAssignment Bs BD Bz k L h h' hs hs') := by
  have he := supported_history_budget_eq_weight Bs BD Bz k L K C ε h h' hs hs'
  exact ⟨(canonicalUnitBulkAverage_le_budget hcount K h h' hs hs' m hm).trans_eq he,
    (canonicalMixedBulkAverage_le_budget hcount K h h' hs hs' m hm).trans_eq he⟩

theorem paired_weight_nonneg (S : List Bool → Finset (ℤ × ℤ)) (C : NNReal) (ε : ℝ)
    {l : ℕ} {p : List Bool} (x : Assignment S l p) :
    0 ≤ weight S (PairedFrequencyTreeSum.factor (C:ℝ) ε) x := by
  induction l generalizing p with
  | zero => exact zero_le_one
  | succ l ih =>
    exact mul_nonneg (mul_nonneg
      (mul_nonneg C.property (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (ih x.2.1)) (ih x.2.2)

theorem sum_supported_bulk_average_le_total {ε : ℝ} {C : NNReal}
    (hcount : LeafCountConstant ε C) (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    (K l m : ℕ) (hm : 0 < m) {ι : Type} [Fintype ι]
    (h h' : ι → History l) (outside : List ℕ)
    (hs : ∀i,(h i).Supported (frequencyBound Bs BD Bz k L) outside)
    (hs' : ∀i,(h' i).Supported (frequencyBound Bs BD Bz k L) outside)
    (hinj : Function.Injective (fun i =>
      supportedHistoryAssignment Bs BD Bz k L (h i) (h' i) (hs i) (hs' i))) :
    (∑i,canonicalUnitBulkAverage K (h i) (h' i) (hs i) (hs' i) m) ≤
      total (pairedRanges Bs BD Bz k L l) (PairedFrequencyTreeSum.factor (C:ℝ) ε) l [] ∧
    (∑i,canonicalMixedBulkAverage K (h i) (h' i) (hs i) (hs' i) m) ≤
      total (pairedRanges Bs BD Bz k L l) (PairedFrequencyTreeSum.factor (C:ℝ) ε) l [] := by
  classical
  have hw : (∑i,weight (pairedRanges Bs BD Bz k L l)
      (PairedFrequencyTreeSum.factor (C:ℝ) ε)
      (supportedHistoryAssignment Bs BD Bz k L (h i) (h' i) (hs i) (hs' i))) ≤
      total (pairedRanges Bs BD Bz k L l) (PairedFrequencyTreeSum.factor (C:ℝ) ε) l [] := by
    apply Finset.sum_le_sum_of_injOn
      (fun i => supportedHistoryAssignment Bs BD Bz k L (h i) (h' i) (hs i) (hs' i))
      hinj.injOn (Finset.subset_univ _)
    · intro i _; exact le_rfl
    · intro x _ _; exact paired_weight_nonneg _ C ε x
  constructor
  · exact (Finset.sum_le_sum (fun i _ =>
      (canonical_bulk_average_le_weight hcount Bs BD Bz k L K (h i) (h' i)
        (hs i) (hs' i) m hm).1)).trans hw
  · exact (Finset.sum_le_sum (fun i _ =>
      (canonical_bulk_average_le_weight hcount Bs BD Bz k L K (h i) (h' i)
        (hs i) (hs' i) m hm).2)).trans hw

end Ostmann.Arithmetic.HistoryPairedFrequencyAverage

end

end OAI
