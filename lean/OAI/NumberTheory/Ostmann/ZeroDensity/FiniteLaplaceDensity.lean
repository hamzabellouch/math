import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.PSeries
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace OAI

namespace Ostmann
open scoped Classical BigOperators

theorem finite_exp_density_square_sum {ι : Type*} (S : Finset ι)
    (y : ι → ℝ) (A B : ℝ) (hB : 0 ≤ B)
    (hy : ∀ i ∈ S, 0 ≤ y i)
    (hc : ∀ t : ℝ, 0 ≤ t →
      ((S.filter (fun i => y i ≤ t)).card : ℝ) ≤ B * Real.exp (A * t)) :
    (∑ i ∈ S, Real.exp (-(2 * A) * y i)) ≤
      B ^ 2 * ∑ j ∈ Finset.range S.card, ((j + 1 : ℕ) : ℝ)⁻¹ ^ 2 := by
  revert hy hc
  refine Finset.strongInductionOn S ?_
  intro S ih hy hc
  by_cases hn : S.Nonempty
  · obtain ⟨i, hi, hmax⟩ := S.exists_max_image y hn
    have hf : S.filter (fun j => y j ≤ y i) = S := by
      apply Finset.filter_eq_self.mpr
      exact hmax
    have hcard := hc (y i) (hy i hi)
    rw [hf] at hcard
    have hn0 : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hn
    have hm := mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg (-(A * y i)))
    have he : Real.exp (A * y i) * Real.exp (-(A * y i)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [mul_assoc, he, mul_one] at hm
    have hpoint : Real.exp (-(2 * A) * y i) ≤ B ^ 2 * (S.card : ℝ)⁻¹ ^ 2 := by
      have hd : Real.exp (-(A * y i)) ≤ B / S.card := by
        apply (le_div_iff₀ hn0).mpr
        simpa only [mul_comm] using hm
      have hs := (sq_le_sq₀ (Real.exp_nonneg _) (div_nonneg hB hn0.le)).mpr hd
      convert hs using 1
      · rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      · rw [div_pow, div_eq_mul_inv, inv_pow]
    have hrest := ih (S.erase i) (Finset.erase_ssubset hi)
      (fun j hj => hy j (Finset.mem_of_mem_erase hj))
      (fun t ht => (show (((S.erase i).filter (fun j => y j ≤ t)).card : ℝ) ≤
        (S.filter (fun j => y j ≤ t)).card from by
          exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))).trans
          (hc t ht))
    have hsize : (S.erase i).card + 1 = S.card := Finset.card_erase_add_one hi
    rw [← Finset.sum_erase_add S (fun i => Real.exp (-(2 * A) * y i)) hi]
    rw [← hsize, Finset.sum_range_succ, mul_add]
    exact add_le_add hrest (by simpa only [hsize] using hpoint)
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Finset.sum_empty, Finset.card_empty, Finset.range_zero, mul_zero, le_refl]

theorem finite_reciprocal_square_sum_le_two (N : ℕ) :
    (∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ)⁻¹ ^ 2) ≤ 2 := by
  have he : (∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ)⁻¹ ^ 2) =
      ∑ j ∈ Finset.Ioo 0 (N + 1), ((j : ℝ) ^ 2)⁻¹ := by
    have hset : Finset.Ioo 0 (N + 1) = Finset.Ico 1 (N + 1) := by
      ext j
      simp only [Finset.mem_Ioo, Finset.mem_Ico]
      omega
    rw [hset, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, inv_pow, Nat.add_comm]
  rw [he]
  simpa only [Nat.cast_zero, zero_add, div_one] using
    (sum_Ioo_inv_sq_le (α := ℝ) 0 (N + 1))

/-- An exponential counting bound and a zero-free gap give exponential
decay for the whole finite zero sum. Squaring the counting constant is harmless
for the subsequent `exp(-D L)` estimates. -/
theorem finite_laplace_density_bound {ι : Type*} (S : Finset ι)
    (y : ι → ℝ) (A B M u : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hM : 4 * A ≤ M) (hu : 0 ≤ u) (hy : ∀ i ∈ S, u ≤ y i)
    (hc : ∀ t : ℝ, 0 ≤ t →
      ((S.filter (fun i => y i ≤ t)).card : ℝ) ≤ B * Real.exp (A * t)) :
    (∑ i ∈ S, Real.exp (-M * y i)) ≤
      2 * B ^ 2 * Real.exp (-(M * u) / 2) := by
  have hy0 (i) (hi : i ∈ S) : 0 ≤ y i := hu.trans (hy i hi)
  have hM0 : 0 ≤ M := by linarith
  calc
    _ ≤ ∑ i ∈ S, Real.exp (-(M * u) / 2) * Real.exp (-(2 * A) * y i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 := mul_nonneg (sub_nonneg.mpr (hy i hi)) hM0
      have h2 := mul_nonneg (by linarith : 0 ≤ M - 4 * A) (hy0 i hi)
      nlinarith
    _ = Real.exp (-(M * u) / 2) * ∑ i ∈ S, Real.exp (-(2 * A) * y i) :=
      (Finset.mul_sum ..).symm
    _ ≤ Real.exp (-(M * u) / 2) * (B ^ 2 *
        ∑ j ∈ Finset.range S.card, ((j + 1 : ℕ) : ℝ)⁻¹ ^ 2) :=
      mul_le_mul_of_nonneg_left (finite_exp_density_square_sum S y A B hB hy0 hc)
        (Real.exp_nonneg _)
    _ ≤ Real.exp (-(M * u) / 2) * (B ^ 2 * 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (finite_reciprocal_square_sum_le_two S.card) (sq_nonneg B)) (Real.exp_nonneg _)
    _ = _ := by ring

end Ostmann

end OAI
