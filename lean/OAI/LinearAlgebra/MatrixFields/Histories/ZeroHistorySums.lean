import Mathlib
import OAI.LinearAlgebra.MatrixFields.Entropy.InitialLeafRates
import OAI.LinearAlgebra.MatrixFields.Entropy.StageCTerminalRates
import OAI.LinearAlgebra.MatrixFields.Entropy.TerminalStatisticLaws

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldZeroHistorySums

open AllFieldHistory AllFieldParameters AllFieldTerminalStatisticLaws
open AllFieldTerminalRates AllFieldStageCTerminalRates
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def zeroRate {K : ℕ} : TerminalZero K → ℝ
  | .inl h => AllFieldZeroLeafRates.fourRate (aShape h.1.val)
  | .inr h => statisticRate (binaryParameter (bParent h) (bShape h.1.val)) (bWeight h)

private theorem subtype_sum_indicator_inline_MatrixMultiplication_AllFieldZeroHistorySums {A : Type*} [Fintype A]
    (P : A → Prop) [DecidablePred P] [Fintype {a // P a}] (f : A → ℝ) :
    (∑ a : {a // P a}, f a.val) = ∑ a, if P a then f a else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

private theorem sum_subtype_complement {A : Type*} [Fintype A]
    (P : A → Prop) [DecidablePred P]
    [Fintype {a // P a}] [Fintype {a // ¬P a}] (f : A → ℝ) :
    (∑ a : {a // ¬P a}, f a.val) + (∑ a : {a // P a}, f a.val) = ∑ a, f a := by
  rw [subtype_sum_indicator_inline_MatrixMultiplication_AllFieldZeroHistorySums (fun a => ¬P a) f, subtype_sum_indicator_inline_MatrixMultiplication_AllFieldZeroHistorySums P f,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : P a <;> simp [ha]

private theorem list_filter_sum_inline_MatrixMultiplication_AllFieldZeroHistorySums {A : Type*} (xs : List A) (p : A → Bool)
    (f : A → ℝ) :
    ((xs.filter p).map f).sum = (xs.map (fun a => if p a then f a else 0)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => cases hp : p a <;> simp [hp, ih]

theorem sum_placement_rate {K : ℕ} {H : Type*} [Fintype H]
    (allocation : Allocation) (canonical : H → CanonicalHistory K) (f : H → ℝ) :
    (∑ h : H × Placement, (amount allocation (canonical h.1, h.2) : ℝ) * f h.1) =
      ∑ h : H, (canonicalAmount allocation (canonical h) : ℝ) * f h := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  change (∑ phi : Placement, (amount allocation (canonical h, phi) : ℝ) * f h) =
    (canonicalAmount allocation (canonical h) : ℝ) * f h
  rw [← Finset.sum_mul]
  have hm : (∑ phi : Placement, (amount allocation (canonical h, phi) : ℝ)) =
      (canonicalAmount allocation (canonical h) : ℝ) := by
    exact_mod_cast sum_placement_amount allocation (canonical h)
  rw [hm]

theorem a_zero_canonical_rate (K : ℕ) :
    (∑ h : {h : AfterA K // aShape h ∉ positiveSecond},
      (aAmount h.val : ℝ) * AllFieldZeroLeafRates.fourRate (aShape h.val)) =
      (K : ℝ) * S1 := by
  rw [subtype_sum_indicator_inline_MatrixMultiplication_AllFieldZeroHistorySums (fun h : AfterA K => aShape h ∉ positiveSecond)
    (fun h => (aAmount h : ℝ) * AllFieldZeroLeafRates.fourRate (aShape h))]
  calc
    _ = ∑ h : AfterA K, (aAmount h : ℝ) *
        (if aShape h ∉ positiveSecond then AllFieldZeroLeafRates.fourRate (aShape h)
          else 0) := by
      apply Finset.sum_congr rfl
      intro h _
      split_ifs <;> simp
    _ = _ := by
      rw [a_history_sum K (fun t =>
        if t ∉ positiveSecond then AllFieldZeroLeafRates.fourRate t else 0),
        S1, zeroSecond, list_filter_sum_inline_MatrixMultiplication_AllFieldZeroHistorySums]
      apply congrArg (fun r : ℝ => (K : ℝ) * r)
      apply congrArg List.sum
      apply List.map_congr_left
      intro t ht
      cases hp : positive t <;> simp [positiveSecond, ht, hp]

theorem a_zero_history_rate (K : ℕ) (allocation : Allocation) :
    (∑ h : AZero K, (amount allocation (history (.inl h)) : ℝ) *
      AllFieldZeroLeafRates.fourRate (aShape h.1.val)) = (K : ℝ) * S1 := by
  calc
    _ = ∑ h : {h : AfterA K // aShape h ∉ positiveSecond},
        (aAmount h.val : ℝ) * AllFieldZeroLeafRates.fourRate (aShape h.val) := by
      exact sum_placement_rate (H := {h : AfterA K // aShape h ∉ positiveSecond})
        allocation (fun h => .afterA h.val)
        (fun h => AllFieldZeroLeafRates.fourRate (aShape h.val))
    _ = _ := a_zero_canonical_rate K

theorem b_positive_secondLeafRate (K : ℕ) :
    (∑ h : BPositive K, (bAmount h.val : ℝ) *
      secondLeafRate (aShape h.val.1.val) (bShape h.val)) = (K : ℝ) * interiorS2 := by
  calc
    _ = ∑ h : BPositive K, (bAmount h.val : ℝ) *
        (2 - (binaryParameter (aShape h.val.1.val) (bShape h.val) : ℝ)) *
          Real.log 5 := by
      apply Finset.sum_congr rfl
      intro h _
      rw [secondLeafRate_positive _ h.val.1.property _ (bShape_mem h.val) h.property]
      ring
    _ = _ := bPositive_rate_eq_interior K

theorem b_zero_canonical_rate (K : ℕ) :
    (∑ h : {h : AfterB K // positive (bShape h) ≠ true},
      (bAmount h.val : ℝ) * secondLeafRate (aShape h.val.1.val) (bShape h.val)) +
      (K : ℝ) * interiorS2 = (K : ℝ) * S2 := by
  rw [← b_positive_secondLeafRate K]
  rw [sum_subtype_complement (fun h : AfterB K => positive (bShape h) = true)
    (fun h => (bAmount h : ℝ) * secondLeafRate (aShape h.1.val) (bShape h))]
  exact b_history_sum K secondLeafRate

theorem b_zero_rate_eq_secondLeafRate {K : ℕ} (h : BZero K) :
    statisticRate (binaryParameter (bParent h) (bShape h.1.val)) (bWeight h) =
      secondLeafRate (aShape h.1.val.1.val) (bShape h.1.val) := by
  have hz : positive (bShape h.1.val) = false := by simpa using h.1.property
  exact (secondLeafRate_zero _ h.1.val.1.property _ (bShape_mem h.1.val) hz).symm

theorem b_zero_history_rate (K : ℕ) (allocation : Allocation) :
    (∑ h : BZero K, (amount allocation (history (.inr h)) : ℝ) *
      statisticRate (binaryParameter (bParent h) (bShape h.1.val)) (bWeight h)) +
      (K : ℝ) * interiorS2 = (K : ℝ) * S2 := by
  have he : (∑ h : BZero K, (amount allocation (history (.inr h)) : ℝ) *
        statisticRate (binaryParameter (bParent h) (bShape h.1.val)) (bWeight h)) =
      ∑ h : {h : AfterB K // positive (bShape h) ≠ true},
        (bAmount h.val : ℝ) * secondLeafRate (aShape h.val.1.val) (bShape h.val) := by
    simp_rw [b_zero_rate_eq_secondLeafRate]
    exact sum_placement_rate (H := {h : AfterB K // positive (bShape h) ≠ true})
      allocation (fun h => .afterB h.val)
      (fun h => secondLeafRate (aShape h.val.1.val) (bShape h.val))
  rw [he]
  exact b_zero_canonical_rate K

theorem zero_history_sum (K : ℕ) (allocation : Allocation) :
    (∑ h : TerminalZero K, (amount allocation (history h) : ℝ) * zeroRate h) =
      (K : ℝ) * (S1 + S2 - interiorS2) := by
  rw [Fintype.sum_sum_type]
  simp only [zeroRate]
  rw [a_zero_history_rate K allocation]
  have hb := b_zero_history_rate K allocation
  nlinarith

end MatrixMultiplication.AllFieldZeroHistorySums

end

end MatrixAllFields

end OAI
