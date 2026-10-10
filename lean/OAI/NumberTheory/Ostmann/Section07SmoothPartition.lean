import OAI.NumberTheory.Ostmann.Section07SmoothPartitionBasic

namespace OAI

namespace Ostmann
open MeasureTheory Set

theorem smoothPartition_translate_zero (x : ℝ) (n : ℤ)
    (hn : n ∉ ({⌊x⌋, ⌊x⌋ + 1} : Finset ℤ)) : smoothPartition (x - n) = 0 := by
  have hn₁ : n ≠ ⌊x⌋ := fun h => hn (by simp [h])
  have hn₂ : n ≠ ⌊x⌋ + 1 := fun h => hn (by simp [h])
  have hx₀ := Int.floor_le x
  have hx₁ := Int.lt_floor_add_one x
  by_cases h : n < ⌊x⌋
  · have hi : n + 1 ≤ ⌊x⌋ := by omega
    have hir : (n : ℝ) + 1 ≤ (⌊x⌋ : ℝ) := by exact_mod_cast hi
    exact smoothPartition_zero_of_one_le (by linarith)
  · have hi : ⌊x⌋ + 2 ≤ n := by omega
    have hir : (⌊x⌋ : ℝ) + 2 ≤ (n : ℝ) := by exact_mod_cast hi
    exact smoothPartition_zero_of_le_neg_one (by linarith)

theorem smoothPartition_translate_summable (x : ℝ) :
    Summable (fun n : ℤ => smoothPartition (x - n)) :=
  summable_of_ne_finset_zero (smoothPartition_translate_zero x)

theorem smoothPartition_translate_tsum (x : ℝ) :
    (∑' n : ℤ, smoothPartition (x - n)) = 1 := by
  rw [tsum_eq_sum (smoothPartition_translate_zero x)]
  have hn : ⌊x⌋ ≠ ⌊x⌋ + 1 := by omega
  rw [Finset.sum_pair hn]
  have hx₀ := Int.floor_le x
  have hx₁ := Int.lt_floor_add_one x
  simp only [smoothPartition, Int.cast_add, Int.cast_one]
  have heq : x - ((⌊x⌋ : ℝ) + 1) + 1 = x - (⌊x⌋ : ℝ) := by ring
  rw [heq, Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.zero_of_nonpos (x := x - ((⌊x⌋ : ℝ) + 1)) (by linarith)]
  ring

theorem smoothPartition_integral : (∫ x : ℝ, smoothPartition x) = 1 := by
  have hs : Function.support smoothPartition ⊆ Ioc (-1) 1 :=
    smoothPartition_support_subset.trans Ioo_subset_Ioc_self
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hs]
  have hg := Real.smoothTransition.continuous
  have hgshift : Continuous (fun x : ℝ => Real.smoothTransition (x + 1)) := by fun_prop
  change (∫ x in (-1 : ℝ)..1,
    Real.smoothTransition (x + 1) - Real.smoothTransition x) = 1
  rw [intervalIntegral.integral_sub (hgshift.intervalIntegrable (-1) 1) (hg.intervalIntegrable (-1) 1),
    intervalIntegral.integral_comp_add_right]
  norm_num only [neg_add_cancel, one_add_one_eq_two]
  have h₀ : (∫ x in (-1 : ℝ)..0, Real.smoothTransition x) = 0 := by
    have heq : (∫ x in (-1 : ℝ)..0, Real.smoothTransition x) = ∫ x in (-1 : ℝ)..0, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact Real.smoothTransition.zero_of_nonpos (by simpa using hx.2)
    rw [heq]
    simp
  have h₁ : (∫ x in (1 : ℝ)..2, Real.smoothTransition x) = 1 := by
    have heq : (∫ x in (1 : ℝ)..2, Real.smoothTransition x) = ∫ x in (1 : ℝ)..2, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact Real.smoothTransition.one_of_one_le (by simpa using hx.1)
    rw [heq]
    norm_num
  have hleft := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ := volume) (-1) 0)
    (hg.intervalIntegrable (μ := volume) 0 1)
  have hright := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ := volume) 0 1)
    (hg.intervalIntegrable (μ := volume) 1 2)
  rw [h₀, zero_add] at hleft
  rw [h₁] at hright
  linarith

end Ostmann

end OAI
