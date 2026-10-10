import Mathlib
import OAI.Probability.ThorpCompatibility.ClumpMoments

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
open Finset
lemma sum_finset_card {α : Type*} [Fintype α] (f : ℕ → ℝ) :
    (∑ s : Finset α, f s.card) =
      ∑ h ∈ Finset.range (Fintype.card α + 1), (Nat.choose (Fintype.card α) h : ℝ) * f h := by
  have hmap : ∀ s ∈ (Finset.univ : Finset (Finset α)),
      s.card ∈ Finset.range (Fintype.card α + 1) := by
    intro s _
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ s))
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun s => f s.card)]
  apply Finset.sum_congr rfl
  intro h _
  have hfilter : Finset.univ.filter (fun s : Finset α => s.card = h) =
      Finset.powersetCard h (Finset.univ : Finset α) := by
    ext s
    simp [Finset.mem_powersetCard]
  calc
    _ = ∑ s ∈ Finset.univ.filter (fun s : Finset α => s.card = h), f h := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [(Finset.mem_filter.mp hs).2]
    _ = _ := by simp [hfilter, Finset.card_powersetCard]

lemma choose_poisson_bound (a h : ℕ) (hh : 0 < h) (t : ℝ) (ht : 0 ≤ t) :
    (a.choose h : ℝ) * t ^ h ≤ (Real.exp 1 * a * t / h) ^ h := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hbase : 0 < ((h : ℝ) / Real.exp 1) ^ h := by positivity
  have hf := descFactorial_exponential_lower h h (le_refl h)
  rw [Nat.descFactorial_self] at hf
  calc
    _ ≤ ((a : ℝ) ^ h / h.factorial) * t ^ h :=
      mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div h a) (pow_nonneg ht _)
    _ ≤ ((a : ℝ) ^ h / ((h : ℝ) / Real.exp 1) ^ h) * t ^ h := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg ht _)
      exact div_le_div_of_nonneg_left (by positivity) hbase hf
    _ = _ := by
      rw [← div_pow, ← mul_pow]
      congr 1
      field_simp

lemma binomial_large_size_term (a h : ℕ) (H t : ℝ) (hH : 0 ≤ H) (ht : 0 ≤ t)
    (hsmall : Real.exp 2 * a * t ≤ H) (hh : H < h) :
    (a.choose h : ℝ) * t ^ h ≤ Real.exp (-H) := by
  have hh' : (0 : ℝ) < h := lt_of_le_of_lt hH hh
  have hhN : 0 < h := by exact_mod_cast hh'
  have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have hbase : Real.exp 1 * a * t / h ≤ 1 / Real.exp 1 := by
    apply (div_le_div_iff₀ hh' (Real.exp_pos _)).mpr
    rw [he] at hsmall
    nlinarith
  calc
    _ ≤ (Real.exp 1 * a * t / h) ^ h := choose_poisson_bound a h hhN t ht
    _ ≤ (1 / Real.exp 1) ^ h := pow_le_pow_left₀ (by positivity) hbase _
    _ = Real.exp (-(h : ℝ)) := by
      rw [one_div, ← Real.exp_neg, ← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (-H) := Real.exp_le_exp.mpr (neg_le_neg hh.le)

lemma binomial_large_size_sum (a : ℕ) (H t : ℝ) (hH : 0 ≤ H) (ht : 0 ≤ t)
    (hsmall : Real.exp 2 * a * t ≤ H) :
    (∑ h ∈ Finset.range (a + 1),
      if h = 0 then (1 : ℝ) else if H < h then (a.choose h : ℝ) * t ^ h else 0) ≤
        1 + (a + 1 : ℕ) * Real.exp (-H) := by
  calc
    _ ≤ ∑ h ∈ Finset.range (a + 1), ((if h = 0 then (1 : ℝ) else 0) + Real.exp (-H)) := by
      apply Finset.sum_le_sum
      intro h _
      by_cases hz : h = 0
      · simp [hz, (Real.exp_pos (-H)).le]
      · by_cases hh : H < h
        · simpa [hz, hh] using binomial_large_size_term a h H t hH ht hsmall hh
        · simp [hz, hh, (Real.exp_pos (-H)).le]
    _ = _ := by simp [Finset.sum_add_distrib]

lemma clumpWeight_eq_card {α : Type*} (H z : ℝ) (s : Finset α) :
    clumpWeight H z s =
      if s.card = 0 then 1 else if H < s.card then Real.exp (z * s.card) else 0 := by
  by_cases hs : s = ∅
  · simp [hs, clumpWeight]
  · have hc : s.card ≠ 0 := fun h => hs (Finset.card_eq_zero.mp h)
    simp [clumpWeight, hs, hc]

lemma clump_subset_sum {α : Type*} [Fintype α] (H z ρ : ℝ) :
    (∑ s : Finset α, clumpWeight H z s * ρ ^ s.card) =
      ∑ h ∈ Finset.range (Fintype.card α + 1),
        if h = 0 then 1 else if H < h then
          (Nat.choose (Fintype.card α) h : ℝ) * (Real.exp z * ρ) ^ h else 0 := by
  simp_rw [clumpWeight_eq_card]
  rw [sum_finset_card (α := α) (fun h =>
    (if h = 0 then (1 : ℝ) else if H < h then Real.exp (z * h) else 0) * ρ ^ h)]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hz : h = 0
  · simp [hz]
  · by_cases hh : H < h
    · simp only [ite_eq_right hz, ite_eq_left hh]
      rw [mul_comm z (h : ℝ), Real.exp_nat_mul, mul_pow]
    · simp [hz, hh]

end ThorpCompatibility

end OAI
