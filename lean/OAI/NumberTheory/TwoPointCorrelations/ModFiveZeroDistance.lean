import OAI.NumberTheory.TwoPointCorrelations.ModFiveLowZeros
import OAI.NumberTheory.TwoPointCorrelations.ModFiveZeroCount

namespace OAI

/-! Quantitative separation between the inner evaluation point and all zeros
in the fixed disk, using the zero-free strip for the modulus-five L-functions.
-/

namespace TwoPointCorrelations

open Complex
open scoped Classical

lemma modFive_log_height_ge_half (t : ℝ) : 1 / 2 ≤ Real.log (|t| + 2) := by
  have hlog : 1 / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  exact hlog.trans (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))

lemma modFive_physical_zero_height (χ : DirichletCharacter ℂ 5) (t : ℝ)
    {ρ : ℂ} (hρ : ρ ∈ modFiveNormalizedZeros χ t) :
    |(modFivePhysicalPoint t ρ).im| ≤ |t| + 2 := by
  have hn : ‖ρ‖ ≤ 7 / 8 := by simpa using hρ.1
  have hi := (Complex.abs_im_le_norm ρ).trans hn
  have he : (modFivePhysicalPoint t ρ).im = t + (3 / 2 : ℝ) * ρ.im := by
    simp [modFivePhysicalPoint, Complex.mul_im]
  rw [he]
  calc
    _ ≤ |t| + |(3 / 2 : ℝ) * ρ.im| := abs_add_le _ _
    _ = |t| + (3 / 2 : ℝ) * |ρ.im| := by rw [abs_mul]; norm_num
    _ ≤ _ := by linarith

lemma modFive_physical_zero_log_height (χ : DirichletCharacter ℂ 5) (t : ℝ)
    {ρ : ℂ} (hρ : ρ ∈ modFiveNormalizedZeros χ t) :
    Real.log (|(modFivePhysicalPoint t ρ).im| + 2) ≤ 2 * Real.log (|t| + 2) := by
  calc
    _ ≤ Real.log ((|t| + 2) ^ 2) := by
      apply Real.log_le_log (by positivity)
      have h := modFive_physical_zero_height χ t hρ
      nlinarith [abs_nonneg t, sq_nonneg (|t|)]
    _ = _ := by rw [Real.log_pow]; norm_num

lemma modFive_zero_distance_of_strip {c : ℝ} (hc : 0 < c)
    (hfree : ∀ (χ : DirichletCharacter ℂ 5), χ ≠ 1 → ∀ (t β : ℝ),
      1 - c / Real.log (|t| + 2) ≤ β →
        DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * (t : ℂ)) ≠ 0)
    (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1) (t σ : ℝ)
    (hσ : 1 - c / (4 * Real.log (|t| + 2)) ≤ σ)
    {ρ : ℂ} (hρ : ρ ∈ modFiveNormalizedZeros χ t) :
    c / (6 * Real.log (|t| + 2)) ≤ ‖modFiveRealDiskPoint σ - ρ‖ := by
  let v := modFivePhysicalPoint t ρ
  have hzero : DirichletCharacter.LFunction χ ((v.re : ℂ) + Complex.I * (v.im : ℂ)) = 0 := by
    have he : (v.re : ℂ) + Complex.I * (v.im : ℂ) = v := by
      apply Complex.ext <;> simp
    rw [he]
    exact modFiveNormalizedZeros_physical_zero χ t hρ
  have hv : v.re < 1 - c / Real.log (|v.im| + 2) := by
    by_contra! h
    exact hfree χ hχ v.im v.re h hzero
  have hH := modFive_log_height_pos t
  have hvH := modFive_log_height_pos v.im
  have hlog := modFive_physical_zero_log_height χ t hρ
  have hinv : c / (2 * Real.log (|t| + 2)) ≤ c / Real.log (|v.im| + 2) :=
    div_le_div_of_nonneg_left hc.le hvH hlog
  have hgap : c / (4 * Real.log (|t| + 2)) ≤ σ - v.re := by
    have he : c / (2 * Real.log (|t| + 2)) = 2 * (c / (4 * Real.log (|t| + 2))) := by ring
    rw [he] at hinv
    linarith
  have hre : (modFiveRealDiskPoint σ - ρ).re = (2 / 3 : ℝ) * (σ - v.re) := by
    dsimp [modFiveRealDiskPoint, v, modFivePhysicalPoint]
    simp only [Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]
    norm_num
    ring
  calc
    _ = (2 / 3 : ℝ) * (c / (4 * Real.log (|t| + 2))) := by ring
    _ ≤ (2 / 3 : ℝ) * (σ - v.re) := mul_le_mul_of_nonneg_left hgap (by norm_num)
    _ = (modFiveRealDiskPoint σ - ρ).re := hre.symm
    _ ≤ |(modFiveRealDiskPoint σ - ρ).re| := le_abs_self _
    _ ≤ _ := Complex.abs_re_le_norm _

end TwoPointCorrelations

end OAI
