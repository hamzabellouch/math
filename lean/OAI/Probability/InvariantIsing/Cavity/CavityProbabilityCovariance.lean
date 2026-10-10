import OAI.Probability.InvariantIsing.Cavity.CavityGibbsMeasureCovariance
import OAI.Probability.InvariantIsing.Cavity.CavityRotationProbability

namespace OAI

/-! Gaussian covariance determines the law of the everywhere defined
Gibbs probability, including its zero-partition convention. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem cavity_gibbs_probability_same_covariance {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (A C : X → ℕ →₀ ℝ)
    (hcov : ∀ x y, cylinderCross (A x) (A y) = cylinderCross (C x) (C y)) :
    gaussianCoordinates.map (fun z => gibbsProbability ν (fun x => H x+cylinderField (A x) z)) =
      gaussianCoordinates.map (fun z => gibbsProbability ν (fun x => H x+cylinderField (C x) z)) := by
  let G : (X → ℝ) → Measure X := fun w => gibbsProbability ν (fun x => H x+w x)
  have hm : Measurable (fun p : (X → ℝ) × X => H p.2+p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro x
    exact (measurable_pi_apply x : Measurable (fun w : X → ℝ => w x)).const_add (H x)
  have hG : Measurable G := measurable_gibbsProbability (ν := fun _ => ν) measurable_const hm
  have hA : Measurable (fun z x => cylinderField (A x) z) :=
    Measurable.of_eval (fun x => measurable_cylinderField (A x))
  have hC : Measurable (fun z x => cylinderField (C x) z) :=
    Measurable.of_eval (fun x => measurable_cylinderField (C x))
  have hh := congrArg (fun μ : Measure (X → ℝ) => μ.map G) (cylinder_fields_law_eq A C hcov)
  simpa only [Measure.map_map hG hA, Measure.map_map hG hC, Function.comp_def, G] using hh

end InvariantIsing

end

end OAI
