import OAI.MeasureTheory.Falconer.Slicing.GaussianSmoothing
import OAI.MeasureTheory.Falconer.Slicing.GaussianShellEnergy
import OAI.MeasureTheory.Falconer.Shells.FrequencyShell

namespace OAI

/-! # Integrating Gaussian smoothing against the actual frequency law -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem gaussian_smoothing_lintegral (β : Measure (Space d)) [IsFiniteMeasure β]
    (v : Space d) :
    ENNReal.ofReal (‖PlanarFalconer.sourceFourier (gaussianDampedMeasure β) v‖^2) ≤
      ENNReal.ofReal (((Real.pi/2)^((d:ℝ)/2))⁻¹)*
        ∫⁻ u : Space d, ENNReal.ofReal (Real.exp (-2*‖u-v‖^2))*
          ENNReal.ofReal (‖PlanarFalconer.sourceFourier β u‖^2) := by
  have h := ENNReal.ofReal_le_ofReal (gaussian_smoothing_square β v)
  rw [ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal (gaussian_fourier_power_integrable β v 2)
      (by filter_upwards with u; positivity)] at h
  convert h using 2
  apply lintegral_congr
  intro u
  exact (ENNReal.ofReal_mul (Real.exp_pos _).le).symm

theorem gaussian_integrated_smoothing (β ρ : Measure (Space d))
    [IsFiniteMeasure β] [IsFiniteMeasure ρ]
    {B A q : ℝ} {k : ℕ} (hB : 1 ≤ B) (hA : 0 ≤ A) (hq : q ≤ k)
    (hsupport : ∀ᵐ v ∂ρ, ‖v‖ ≤ 2*B)
    (hball : ∀ x : Space d, ∀ r : ℝ, 1 ≤ r →
      ρ (ball x r) ≤ ENNReal.ofReal (A*r^q)) :
    (∫⁻ v, ENNReal.ofReal (‖PlanarFalconer.sourceFourier (gaussianDampedMeasure β) v‖^2) ∂ρ) ≤
      ENNReal.ofReal ((((Real.pi/2)^((d:ℝ)/2))⁻¹)*(Real.exp 1*A*gaussianBallConstant k))*
        ∫⁻ u : Space d, ENNReal.ofReal (Real.exp (-‖u‖^2/(16*B^2)))*
          ENNReal.ofReal (‖PlanarFalconer.sourceFourier β u‖^2) := by
  let C : ℝ := ((Real.pi/2)^((d:ℝ)/2))⁻¹
  let D : ℝ := Real.exp 1*A*gaussianBallConstant k
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (Real.exp_pos _).le hA) (gaussianBallConstant_nonneg k)
  have hswap : (∫⁻ v, ∫⁻ u : Space d, ENNReal.ofReal (Real.exp (-2*‖u-v‖^2))*
      ENNReal.ofReal (‖PlanarFalconer.sourceFourier β u‖^2) ∂volume ∂ρ) =
      ∫⁻ u : Space d, ∫⁻ v, ENNReal.ofReal (Real.exp (-2*‖u-v‖^2))*
        ENNReal.ofReal (‖PlanarFalconer.sourceFourier β u‖^2) ∂ρ ∂volume := by
    apply lintegral_lintegral_swap
    unfold PlanarFalconer.sourceFourier
    fun_prop
  have hinner (u : Space d) :
      (∫⁻ v, ENNReal.ofReal (Real.exp (-2*‖u-v‖^2)) ∂ρ) ≤
        ENNReal.ofReal D*ENNReal.ofReal (Real.exp (-‖u‖^2/(16*B^2))) := by
    have hi : Integrable (fun v : Space d => Real.exp (-2*‖u-v‖^2)) ρ := by
      apply (integrable_const (1:ℝ)).mono (by fun_prop)
      filter_upwards with v
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),norm_one]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _))
    rw [← ofReal_integral_eq_lintegral_ofReal hi (by filter_upwards with v; positivity),
      ← ENNReal.ofReal_mul hD]
    apply ENNReal.ofReal_le_ofReal
    simpa only [dist_eq_norm] using gaussian_localized_mass ρ hB hA hq hsupport hball u
  calc
    _ ≤ ∫⁻ v, ENNReal.ofReal C*(∫⁻ u : Space d, ENNReal.ofReal (Real.exp (-2*‖u-v‖^2))*
        ENNReal.ofReal (‖PlanarFalconer.sourceFourier β u‖^2)) ∂ρ :=
      lintegral_mono (gaussian_smoothing_lintegral β)
    _ = ENNReal.ofReal C*(∫⁻ u : Space d, ∫⁻ v,
        ENNReal.ofReal (Real.exp (-2*‖u-v‖^2))*
          ENNReal.ofReal (‖PlanarFalconer.sourceFourier β u‖^2) ∂ρ) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,hswap]
    _ = ENNReal.ofReal C*(∫⁻ u : Space d,
        (∫⁻ v, ENNReal.ofReal (Real.exp (-2*‖u-v‖^2)) ∂ρ)*
          ENNReal.ofReal (‖PlanarFalconer.sourceFourier β u‖^2)) := by
      congr 1
      apply lintegral_congr
      intro u
      exact lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C*(∫⁻ u : Space d,
        (ENNReal.ofReal D*ENNReal.ofReal (Real.exp (-‖u‖^2/(16*B^2))))*
          ENNReal.ofReal (‖PlanarFalconer.sourceFourier β u‖^2)) := by
      gcongr with u
      exact hinner u
    _ = _ := by
      simp_rw [mul_assoc]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,← mul_assoc,← ENNReal.ofReal_mul hC]
      simp only [C,D,mul_assoc]

end Falconer

end OAI
