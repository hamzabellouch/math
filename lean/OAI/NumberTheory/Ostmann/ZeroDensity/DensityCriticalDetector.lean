import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDetectorDichotomy
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityFourierContour
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityKernelPacking

namespace OAI

/-! # The detector in the height convention of the proved moments -/

namespace Ostmann

open Complex MeasureTheory

noncomputable def densityCriticalProduct (χ : PrimitiveComplexCharacter) (X : ℕ)
    (t u : ℝ) : ℂ :=
  χ.L (densityVerticalPoint (1 / 2) (t + u)) *
    densityMollifier X χ.character (densityVerticalPoint (1 / 2) (t + u))

 theorem densityCriticalProduct_continuous (χ : PrimitiveComplexCharacter) (X : ℕ) (t : ℝ) :
    Continuous (densityCriticalProduct χ X t) := by
  have hL : Continuous χ.L := continuous_iff_continuousAt.mpr (fun z => (χ.L_analytic z).continuousAt)
  have hM : Continuous (densityMollifier X χ.character) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    simpa only [zero_add] using (densityMollifier_shift_analytic χ X 0 z).continuousAt
  exact (hL.mul hM).comp (by unfold densityVerticalPoint; fun_prop)

 theorem densityCriticalProduct_bound (χ : PrimitiveComplexCharacter) (X : ℕ) (t u : ℝ) :
    ‖densityCriticalProduct χ X t u‖ ≤
      (2 * ((χ.modulus : ℝ) + 1) * X * (3 + 2 * Real.pi * |t| + 2 * Real.pi)) *
        (1 + |u|) := by
  have hL := density_L_short_positive_bound χ (densityVerticalPoint (1 / 2) (t + u))
    (by simp [densityVerticalPoint]) (by norm_num [densityVerticalPoint])
  have hM := densityMollifier_norm_le χ X (densityVerticalPoint (1 / 2) (t + u))
    (by simp [densityVerticalPoint])
  have ha : |(densityVerticalPoint (1 / 2) (t + u)).im| ≤
      2 * Real.pi * (|t| + |u|) := by
    have him : (densityVerticalPoint (1 / 2) (t + u)).im = 2 * Real.pi * (t + u) := by
      simp [densityVerticalPoint]
    rw [him]
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    exact mul_le_mul_of_nonneg_left (abs_add_le t u) (by positivity)
  have hb : 3 + |(densityVerticalPoint (1 / 2) (t + u)).im| ≤
      (3 + 2 * Real.pi * |t| + 2 * Real.pi) * (1 + |u|) := by
    nlinarith [Real.pi_pos, abs_nonneg t, abs_nonneg u,
      show 0 ≤ 2 * Real.pi * |t| * |u| by positivity]
  rw [densityCriticalProduct, norm_mul]
  apply (mul_le_mul hL hM (norm_nonneg _) (by positivity)).trans
  have h := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ 2 * ((χ.modulus : ℝ) + 1) * X by positivity)
  convert h using 1 <;> ring

 theorem densityCriticalProduct_integrable (χ : PrimitiveComplexCharacter) (X : ℕ) (t : ℝ) :
    Integrable (fun u => densityCubicWeight u * ‖densityCriticalProduct χ X t u‖) := by
  let K := 2 * ((χ.modulus : ℝ) + 1) * X * (3 + 2 * Real.pi * |t| + 2 * Real.pi)
  have hg : Integrable (fun u : ℝ => (1 + |u|) ^ (-(2 : ℝ))) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 2))
  apply (hg.const_mul K).mono'
  · exact ((by
      exact continuous_const.div ((continuous_const.add continuous_abs).pow 3)
        (fun u => by positivity) : Continuous densityCubicWeight).mul
      (densityCriticalProduct_continuous χ X t).norm).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (densityCubicWeight_nonneg _) (norm_nonneg _))]
    calc
      _ ≤ densityCubicWeight u * (K * (1 + |u|)) :=
        mul_le_mul_of_nonneg_left (densityCriticalProduct_bound χ X t u) (densityCubicWeight_nonneg u)
      _ = K * (1 + |u|) ^ (-(2 : ℝ)) := by
        rw [densityCubicWeight, Real.rpow_neg (by positivity), Real.rpow_ofNat]
        field_simp

 theorem densityCubicWeight_scaled (u : ℝ) :
    densityCubicWeight (2 * Real.pi * u) ≤ densityCubicWeight u := by
  unfold densityCubicWeight
  apply one_div_le_one_div_of_le (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  nlinarith [Real.pi_gt_three, abs_nonneg u]

 theorem densityDetector_scaled_bound (χ : PrimitiveComplexCharacter) (X : ℕ)
    (β t : ℝ) (hβ : 1 / 2 < β) (hβ1 : β ≤ 1) (Y : ℝ) (hY : 1 ≤ Y) (u : ℝ) :
    ‖densityDetectorIntegrand χ X (densityVerticalPoint β t) Y
      (((1 / 2 - β : ℝ) : ℂ) + (2 * Real.pi * u : ℝ) * I)‖ ≤
      (16 * Y ^ (1 / 2 - β) / (β - 1 / 2)) *
        (densityCubicWeight u * ‖densityCriticalProduct χ X t u‖) := by
  have he : densityVerticalPoint β t + (((1 / 2 - β : ℝ) : ℂ) + (2 * Real.pi * u : ℝ) * I) =
      densityVerticalPoint (1 / 2) (t + u) := by
    unfold densityVerticalPoint
    push_cast
    ring
  have hk := densityDetectorKernel_left_bound (β - 1 / 2) (2 * Real.pi * u)
    (by linarith) (by linarith)
  rw [← Complex.ofReal_neg, show -(β - 1 / 2) = 1 / 2 - β by ring,
    ← densityCubicWeight_rpow] at hk
  have hk' := hk.trans (mul_le_mul_of_nonneg_left (densityCubicWeight_scaled u) (by positivity))
  rw [densityDetectorIntegrand, norm_mul, norm_mul, he,
    Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < Y)]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
    sub_zero, add_zero]
  have hh := mul_le_mul_of_nonneg_left hk'
    (show 0 ≤ ‖densityCriticalProduct χ X t u‖ * Y ^ (1 / 2 - β) by positivity)
  convert hh using 1 <;> dsimp [densityCriticalProduct]
  ring

 theorem densityDetectorMean_at_zero_bound (χ : PrimitiveComplexCharacter) (X : ℕ)
    (β t : ℝ) (hβ : 1 / 2 < β) (hβ1 : β ≤ 1)
    (hz : χ.L (densityVerticalPoint β t) = 0) (Y : ℝ) (hY : 1 ≤ Y) :
    ‖densityDetectorMean χ X (densityVerticalPoint β t) Y‖ ≤
      (16 * Y ^ (1 / 2 - β) / (β - 1 / 2)) *
        ∫ u : ℝ, densityCubicWeight u * ‖densityCriticalProduct χ X t u‖ := by
  rw [densityDetectorMean_at_zero χ X _ (by simpa [densityVerticalPoint] using hβ)
    (by simpa [densityVerticalPoint] using hβ1) hz Y hY]
  have hre : (densityVerticalPoint β t).re = β := by simp [densityVerticalPoint]
  rw [hre]
  have hscale := density_fourier_integral_scale (fun u => densityDetectorIntegrand χ X
    (densityVerticalPoint β t) Y (((1 / 2 - β : ℝ) : ℂ) + u * I))
  have hconst : ((1 / (2 * Real.pi) : ℝ) : ℂ) = (2 * (Real.pi : ℂ))⁻¹ := by
    simp
  rw [hconst]
  change ‖(2 * (Real.pi : ℂ))⁻¹ * (∫ u : ℝ, densityDetectorIntegrand χ X
    (densityVerticalPoint β t) Y (((1 / 2 - β : ℝ) : ℂ) + u * I))‖ ≤ _
  rw [hscale]
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
  · exact (densityCriticalProduct_integrable χ X t).const_mul _
  · exact Filter.Eventually.of_forall (densityDetector_scaled_bound χ X β t hβ hβ1 Y hY)

end Ostmann

end OAI
