import Mathlib.Basic.Complex.BigOperators
import OAI.Analysis.MutuallyUnbiased.Moments.DifferentMatrices

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem triple_difference (i j : Coord) :
    (3 : ℤ) • difference i j = difference i j + difference i j + difference i j := by
  funext k
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

theorem character_triple_difference (x : Coord → ℂ)
    (hx : ∀ i, Complex.normSq (x i) = 1) (i j : Coord) :
    character x ((3 : ℤ) • difference i j) = x i ^ 3 * conj (x j ^ 3) := by
  rw [triple_difference, character_add x (fun i => unit_ne_zero (hx i)),
    character_add x (fun i => unit_ne_zero (hx i)), character_difference x hx, map_pow]
  ring

theorem triple_difference_sum {H : CMatrix} (hH : IsHadamard H) :
    (∑ i, ∑ j, g H ((3 : ℤ) • difference i j)) =
      (6 : ℂ)⁻¹ * ∑ k, (Complex.normSq (∑ i, H i k ^ 3) : ℂ) := by
  simp only [g, character_triple_difference _ (fun i => hH.1 i _)]
  simp only [← Finset.mul_sum]
  congr 1
  calc
    _ = ∑ i, ∑ k, ∑ j, H i k ^ 3 * conj (H j k ^ 3) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, H i k ^ 3 * conj (H j k ^ 3) := Finset.sum_comm
    _ = _ := by simp_rw [sum_mul_conj]

/-- The cubic off-diagonal Fourier sum is bounded below by minus the dimension.
It is the average of squared absolute values of column power sums, minus six. -/
theorem cubic_fourier_nonnegative {H : CMatrix} (hH : IsHadamard H) :
    0 ≤ 6 + offDiagSum (fun i j => (g H ((3 : ℤ) • difference i j)).re) := by
  have h := congrArg Complex.re (offDiagSum_add_diag
    (fun i j => g H ((3 : ℤ) • difference i j)))
  rw [triple_difference_sum hH] at h
  have hd : (∑ i, g H ((3 : ℤ) • difference i i)) = (6 : ℂ) := by
    simp [difference]
  rw [hd] at h
  have hi : (6 : ℂ)⁻¹ = (((6 : ℝ)⁻¹ : ℝ) : ℂ) := by simp
  rw [hi] at h
  simp only [Complex.add_re, offDiagSum, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.re_ofNat] at h
  have hn : 0 ≤ (6 : ℝ)⁻¹ * ∑ k, Complex.normSq (∑ i, H i k ^ 3) := by
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _)
  unfold offDiagSum
  linarith

end MUB6

end

end OAI
