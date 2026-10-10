import OAI.Probability.InvariantIsing.Cavity.CavityIncrementComparison
import OAI.Probability.InvariantIsing.Cavity.CavityVanishingPenalty

namespace OAI

/-! A logarithmic cap preserves the one-sided finite cavity increment
inequality.  The base Gaussian perturbation remains inside the Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_mean_log_tilt_cap_le {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H W R : X → ℝ) {M L D T : ℝ}
    (hH : ∀ x, |H x| ≤ M) (hW : ∀ x, |W x| ≤ L)
    (hR : ∀ x, |R x| ≤ D) (hT : 0 ≤ T) (δ : ℝ)
    (C : X → ℕ →₀ ℝ) {B : ℝ} (hC : ∀ x, (C x).sum (fun _ z => z^2) ≤ B) :
    (∫ z, Real.log (∫ x, Real.exp (min (W x) T - δ * R x)
      ∂ν.tilted (fun x => H x+cylinderField (C x) z)) ∂gaussianCoordinates) ≤
    ∫ z, Real.log (∫ x, Real.exp (W x - δ * R x)
      ∂ν.tilted (fun x => H x+cylinderField (C x) z)) ∂gaussianCoordinates := by
  have hcap x : |min (W x) T| ≤ L := (cavity_abs_min_cap hT).trans (hW x)
  have hpen := cavity_bounded_sub_mul W R δ hW hR
  have hcp := cavity_bounded_sub_mul (fun x => min (W x) T) R δ hcap hR
  rw [cavity_mean_log_tilt_factor ν H _ hH hcp C hC,
    cavity_mean_log_tilt_factor ν H _ hH hpen C hC]
  apply sub_le_sub_right
  apply cylinder_log_mean_mono ν _ _
    (cavity_bounded_base_exp_integrable ν _ (fun x =>
      (abs_add_le _ _).trans (add_le_add (hH x) (hcp x))))
    (cavity_bounded_base_exp_integrable ν _ (fun x =>
      (abs_add_le _ _).trans (add_le_add (hH x) (hpen x)))) C hC
  intro x
  linarith [min_le_left (W x) T]

theorem cavity_capped_log_increment_comparison {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H W J R : X → ℝ) (c d : ℝ)
    {M L M₁ D B₀ B₁ T : ℝ}
    (hH : ∀ x, |H x| ≤ M) (hW : ∀ x, |W x| ≤ L) (hJ : ∀ x, |J x| ≤ M₁)
    (hR : ∀ x, |R x| ≤ D) (hT : 0 ≤ T)
    (hE : ∀ x, |J x - (H x + W x)| ≤ d * R x)
    (C A : X → ℕ →₀ ℝ)
    (hC : ∀ x, (C x).sum (fun _ z => z^2) ≤ B₀)
    (hA : ∀ x, (A x).sum (fun _ z => z^2) ≤ B₁)
    (hK : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤
      c * (R x + R y)) :
    (∫ z, Real.log (∫ x, Real.exp (min (W x) T - (d+2*c)*R x)
      ∂ν.tilted (fun x => H x+cylinderField (C x) z)) ∂gaussianCoordinates) ≤
    (∫ z, Real.log (∫ x, Real.exp (J x+cylinderField (A x) z) ∂ν)
      ∂gaussianCoordinates) -
      ∫ z, Real.log (∫ x, Real.exp (H x+cylinderField (C x) z) ∂ν)
        ∂gaussianCoordinates := by
  exact (cavity_mean_log_tilt_cap_le ν H W R hH hW hR hT (d+2*c) C hC).trans
    (cavity_log_increment_comparison ν H W J R c d hH hW hJ hR hE C A hC hA hK)

end InvariantIsing

end

end OAI
