import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterHighZeros
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterZeroCount

namespace OAI

/-! Horizontal separation of all zeros in the normalized disk from a
point in a narrower high-height strip. -/

namespace TwoPointCorrelations

open Complex
open scoped Classical

variable {q : ℕ} [NeZero q]

lemma mrt_character_physical_zero_height (χ : DirichletCharacter ℂ q) (t : ℝ)
    {rho : ℂ} (hrho : rho ∈ mrtCharacterNormalizedZeros χ t) :
    |(mrtCharacterPhysicalPoint t rho).im| ≤ |t| + 2 := by
  have hn : ‖rho‖ ≤ 7 / 8 := by simpa using hrho.1
  have hi := (Complex.abs_im_le_norm rho).trans hn
  have he : (mrtCharacterPhysicalPoint t rho).im = t + (3 / 2 : ℝ) * rho.im := by
    simp [mrtCharacterPhysicalPoint, Complex.mul_im]
  rw [he]
  calc
    _ ≤ |t| + |(3 / 2 : ℝ) * rho.im| := abs_add_le _ _
    _ = |t| + (3 / 2 : ℝ) * |rho.im| := by rw [abs_mul]; norm_num
    _ ≤ _ := by linarith

lemma mrt_character_physical_zero_height_lower (χ : DirichletCharacter ℂ q) (t : ℝ)
    {rho : ℂ} (hrho : rho ∈ mrtCharacterNormalizedZeros χ t) :
    |t| ≤ |(mrtCharacterPhysicalPoint t rho).im| + 2 := by
  have hn : ‖rho‖ ≤ 7 / 8 := by simpa using hrho.1
  have hi := (Complex.abs_im_le_norm rho).trans hn
  have he : t = (mrtCharacterPhysicalPoint t rho).im - (3 / 2 : ℝ) * rho.im := by
    simp [mrtCharacterPhysicalPoint, Complex.mul_im]
  calc
    _ = |(mrtCharacterPhysicalPoint t rho).im - (3 / 2 : ℝ) * rho.im| := congrArg abs he
    _ ≤ |(mrtCharacterPhysicalPoint t rho).im| + |(3 / 2 : ℝ) * rho.im| := abs_sub _ _
    _ = |(mrtCharacterPhysicalPoint t rho).im| + (3 / 2 : ℝ) * |rho.im| := by
      rw [abs_mul]; norm_num
    _ ≤ _ := by linarith

lemma mrt_character_physical_zero_log_height (χ : DirichletCharacter ℂ q) (t : ℝ)
    {rho : ℂ} (hrho : rho ∈ mrtCharacterNormalizedZeros χ t) :
    mrtCharacterHeight q (mrtCharacterPhysicalPoint t rho).im ≤
      2 * mrtCharacterHeight q t := by
  have hh : Real.log (|(mrtCharacterPhysicalPoint t rho).im| + 2) ≤
      2 * Real.log (|t| + 2) := by
    calc
      _ ≤ Real.log ((|t| + 2) ^ 2) := by
        apply Real.log_le_log (by positivity)
        have h := mrt_character_physical_zero_height χ t hrho
        nlinarith [abs_nonneg t, sq_nonneg (|t|)]
      _ = _ := by rw [Real.log_pow]; norm_num
  have hq : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast NeZero.pos q)
  rw [mrt_character_height_split, mrt_character_height_split]
  linarith

lemma mrt_character_zero_distance_of_strip {c T : ℝ} (hc : 0 < c)
    (χ : DirichletCharacter ℂ q)
    (hfree : ∀ t beta : ℝ, T ≤ |t| →
      1 - c / mrtCharacterHeight q t ≤ beta →
        DirichletCharacter.LFunction χ ((beta : ℂ) + Complex.I * (t : ℂ)) ≠ 0)
    (t sigma : ℝ) (ht : T + 2 ≤ |t|)
    (hsigma : 1 - c / (4 * mrtCharacterHeight q t) ≤ sigma)
    {rho : ℂ} (hrho : rho ∈ mrtCharacterNormalizedZeros χ t) :
    c / (6 * mrtCharacterHeight q t) ≤ ‖mrtCharacterRealDiskPoint sigma - rho‖ := by
  let v := mrtCharacterPhysicalPoint t rho
  have hzero : DirichletCharacter.LFunction χ ((v.re : ℂ) + Complex.I * (v.im : ℂ)) = 0 := by
    have he : (v.re : ℂ) + Complex.I * (v.im : ℂ) = v := by
      apply Complex.ext <;> simp
    rw [he]
    exact mrtCharacterNormalizedZeros_physical_zero χ t hrho
  have hvt : T ≤ |v.im| := by
    have hh := mrt_character_physical_zero_height_lower χ t hrho
    change |t| ≤ |v.im| + 2 at hh
    linarith
  have hv : v.re < 1 - c / mrtCharacterHeight q v.im := by
    by_contra! h
    exact hfree v.im v.re hvt h hzero
  have hH := mrt_character_height_pos q t
  have hvH := mrt_character_height_pos q v.im
  have hlog := mrt_character_physical_zero_log_height χ t hrho
  have hinv : c / (2 * mrtCharacterHeight q t) ≤ c / mrtCharacterHeight q v.im :=
    div_le_div_of_nonneg_left hc.le hvH hlog
  have hgap : c / (4 * mrtCharacterHeight q t) ≤ sigma - v.re := by
    have he : c / (2 * mrtCharacterHeight q t) =
        2 * (c / (4 * mrtCharacterHeight q t)) := by ring
    rw [he] at hinv
    linarith
  have hre : (mrtCharacterRealDiskPoint sigma - rho).re =
      (2 / 3 : ℝ) * (sigma - v.re) := by
    dsimp [mrtCharacterRealDiskPoint, v, mrtCharacterPhysicalPoint]
    simp only [Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]
    norm_num
    ring
  calc
    _ = (2 / 3 : ℝ) * (c / (4 * mrtCharacterHeight q t)) := by ring
    _ ≤ (2 / 3 : ℝ) * (sigma - v.re) := mul_le_mul_of_nonneg_left hgap (by norm_num)
    _ = (mrtCharacterRealDiskPoint sigma - rho).re := hre.symm
    _ ≤ |(mrtCharacterRealDiskPoint sigma - rho).re| := le_abs_self _
    _ ≤ _ := Complex.abs_re_le_norm _

end TwoPointCorrelations

end OAI
