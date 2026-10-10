import OAI.Probability.InvariantIsing.Cavity.CavityReplicaCovarianceLaw
import OAI.Probability.InvariantIsing.Cavity.CavityRandomTiltMoment

namespace OAI

/-! Covariance equality transports the logarithm of an added cavity
weight while retaining the Gaussian field inside the base Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem cavity_log_partition_same_covariance {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) (H : X → ℝ) (A C : X → ℕ →₀ ℝ)
    (hcov : ∀ x y, cylinderCross (A x) (A y) = cylinderCross (C x) (C y)) :
    (∫ z, Real.log (∫ x, Real.exp (H x+cylinderField (A x) z) ∂ν) ∂gaussianCoordinates) =
    ∫ z, Real.log (∫ x, Real.exp (H x+cylinderField (C x) z) ∂ν) ∂gaussianCoordinates := by
  have hm : Measurable (fun p : (X → ℝ) × X => Real.exp (H p.2+p.1 p.2)) := by
    apply measurable_from_prod_countable_left
    intro x
    exact ((measurable_pi_apply x : Measurable (fun w : X → ℝ => w x)).const_add (H x)).exp
  exact cavity_field_functional_same_covariance A C hcov
    (fun w => Real.log (∫ x, Real.exp (H x+w x) ∂ν))
    hm.stronglyMeasurable.integral_prod_right'.measurable.log

theorem cavity_log_weight_same_covariance {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H W : X → ℝ)
    (A C : X → ℕ →₀ ℝ)
    (hcov : ∀ x y, cylinderCross (A x) (A y) = cylinderCross (C x) (C y)) :
    (∫ z, Real.log (∫ x, Real.exp (W x)
      ∂ν.tilted (fun x => H x + cylinderField (A x) z)) ∂gaussianCoordinates) =
    ∫ z, Real.log (∫ x, Real.exp (W x)
      ∂ν.tilted (fun x => H x + cylinderField (C x) z)) ∂gaussianCoordinates := by
  have hm : Measurable (fun p : (X → ℝ) × X => H p.2 + p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro x
    exact (measurable_pi_apply x : Measurable (fun w : X → ℝ => w x)).const_add (H x)
  have hw : Measurable (fun p : (X → ℝ) × X => Real.exp (W p.2)) :=
    ((measurable_of_countable W).comp measurable_snd).exp
  exact cavity_field_functional_same_covariance A C hcov
    (fun w => Real.log (∫ x, Real.exp (W x) ∂ν.tilted (fun x => H x+w x)))
    (measurable_random_tilted_integral measurable_const hm hw).log

end InvariantIsing

end

end OAI
