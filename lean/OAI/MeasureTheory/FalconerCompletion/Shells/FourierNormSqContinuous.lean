import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Fourier.FourierPolynomialSmoothing

namespace OAI

/-! Dyadic shells and prefix decompositions. -/

open _root_.OAI.PlanarFalconer

section
section
namespace CriticalFourierSupport
namespace CurrentFalconer
open MeasureTheory Set
open scoped ENNReal
section HalfDimensionalFourier
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem sourceFourier_norm_sq_continuous (μ : Measure V) [IsFiniteMeasure μ] :
    Continuous (fun v : V => ‖PlanarFalconer.sourceFourier μ v‖^2) := by
  unfold PlanarFalconer.sourceFourier
  fun_prop

theorem sourceFourier_norm_sq_integrable (μ ν : Measure V) [IsProbabilityMeasure μ]
    [IsFiniteMeasure ν] : Integrable (fun v : V => ‖PlanarFalconer.sourceFourier μ v‖^2) ν := by
  apply (integrable_const (μ := ν) (1 : ℝ)).mono'
    (sourceFourier_norm_sq_continuous μ).aestronglyMeasurable
  filter_upwards with v
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _)
    (sourceFourier_norm_le_one μ v) 2

theorem annularFrequencyMeasure_fourier_integral (μ ξ : Measure V)
    [IsProbabilityMeasure μ] [IsFiniteMeasure ξ] (B H : ℝ) :
    (∫ v : V, ‖PlanarFalconer.sourceFourier μ v‖^2 ∂annularFrequencyMeasure ξ B H) =
      ∫ s : ℝ in annularScalarSet B H,
        ∫ w : V, ‖PlanarFalconer.sourceFourier μ (s • w)‖^2 ∂ξ := by
  have hc := sourceFourier_norm_sq_continuous μ
  have hi : Integrable (fun z : ℝ × V =>
      ‖PlanarFalconer.sourceFourier μ (z.1 • z.2)‖^2)
      ((volume.restrict (annularScalarSet B H)).prod ξ) := by
    apply (integrable_const (1 : ℝ)).mono' (hc.comp (by fun_prop)).aestronglyMeasurable
    filter_upwards with z
    change ‖‖PlanarFalconer.sourceFourier μ (z.1 • z.2)‖^2‖ ≤ 1
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _)
      (sourceFourier_norm_le_one μ (z.1 • z.2)) 2
  rw [annularFrequencyMeasure, integral_map (by fun_prop) hc.aestronglyMeasurable]
  exact integral_prod _ hi

theorem halfDimensional_fourier_shell (χ : SchwartzMap V ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ ξ : Measure V), IsProbabilityMeasure μ →
      IsFiniteMeasure ξ → (∀ᵐ x ∂μ, χ x = 1) →
      ∀ (K L B H R : ℝ), 1 ≤ K → 1 ≤ L → 1 ≤ B → B ≤ H → H ≤ R →
      (∀ (x : V) (r : ℝ), H⁻¹ ≤ r → r ≤ 1 →
        μ (Metric.ball x r) ≤ ENNReal.ofReal (K * r^((Module.finrank ℝ V : ℝ)/2))) →
      ξ Set.univ ≤ 1 → (∀ᵐ w ∂ξ, ‖w‖ = 1) →
      (∀ (w : V), ‖w‖ = 1 → ∀ r : ℝ, R⁻¹ ≤ r → r ≤ 1 →
        ξ (Metric.ball w r) ≤ ENNReal.ofReal (L * r^((Module.finrank ℝ V : ℝ)/2))) →
      (∫ s : ℝ in annularScalarSet B H,
        ∫ w : V, ‖PlanarFalconer.sourceFourier μ (s • w)‖^2 ∂ξ) ≤ C*L*K := by
  let S : ℝ := (Module.finrank ℝ V : ℝ)/2
  have hS : 0 ≤ S := by dsimp [S]; positivity
  let F : ℝ := Real.exp 16 * Real.pi^S * gaussianBallConstant S
  have hF : 0 ≤ F := mul_nonneg (mul_nonneg (Real.exp_pos _).le
    (Real.rpow_nonneg Real.pi_pos.le _)) (gaussianBallConstant_nonneg S)
  obtain ⟨C₀,hC₀,hann⟩ := sourceFourier_annular_integral χ
  refine ⟨C₀*(4*2^S*F+1), by positivity, ?_⟩
  intro μ ξ hμ hξ hχ K L B H R hK hL hB hBH hHR hball hmass hsphere hcap
  let := hμ
  let := hξ
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hH0 := hB0.trans_le hBH
  have hK0 : 0 ≤ K := by linarith
  have hL0 : 0 ≤ L := by linarith
  let A : ℝ := 4*L*(2*B⁻¹)^S
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hνball := annularFrequencyMeasure_ball (H := H) ξ hB0 (hBH.trans hHR) hS hL
    hmass hsphere hcap
  have hνmass := annularFrequencyMeasure_mass (H := H) ξ hB0.le hmass
  have hνsupp := annularFrequencyMeasure_support ξ hsphere B H
  have hh := hann μ (annularFrequencyMeasure ξ B H) hμ (by infer_instance)
    hχ A B hA hB0.le hνball hνmass hνsupp
  have hgauss := fourier_ball_integral_le μ hK0 hB0
    (fun x r hr => probability_ball_bound_large_radii μ hS hK hball x r
      (((inv_le_inv₀ hH0 hB0).mpr hBH).trans hr))
  change (∫ u : V in Metric.ball 0 (4*B), ‖PlanarFalconer.sourceFourier μ u‖^2) ≤
    F*K*B^((Module.finrank ℝ V : ℝ)-S) at hgauss
  have hmajor := mul_le_mul_of_nonneg_left hgauss (mul_nonneg hC₀.le hA)
  have hcancel : (2*B⁻¹)^S * B^((Module.finrank ℝ V : ℝ)-S) = 2^S := by
    rw [Real.mul_rpow (by norm_num) (inv_nonneg.mpr hB0.le),
      ← Real.rpow_neg_eq_inv_rpow B S, mul_assoc, ← Real.rpow_add hB0]
    have he : -S + ((Module.finrank ℝ V : ℝ)-S) = 0 := by dsimp [S]; ring
    rw [he, Real.rpow_zero, mul_one]
  have he : C₀*A*(F*K*B^((Module.finrank ℝ V : ℝ)-S)) =
      C₀*(4*2^S*F)*L*K := by
    dsimp only [A]
    calc
      _ = (C₀*4*L*F*K)*((2*B⁻¹)^S * B^((Module.finrank ℝ V : ℝ)-S)) := by ring
      _ = _ := by rw [hcancel]; ring
  rw [he] at hmajor
  rw [← annularFrequencyMeasure_fourier_integral μ ξ B H]
  have hLK : 1 ≤ L*K := by nlinarith
  nlinarith [mul_nonneg hC₀.le (sub_nonneg.mpr hLK)]

end HalfDimensionalFourier
end CurrentFalconer
end CriticalFourierSupport
end
end

end OAI
