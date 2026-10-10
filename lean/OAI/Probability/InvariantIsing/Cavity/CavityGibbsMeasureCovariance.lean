import OAI.Probability.InvariantIsing.Cavity.CavityReplicaCovarianceLaw

namespace OAI

/-! Equality of Gaussian field covariance identifies the law of the
entire random Gibbs measure, so subsequent deterministic cavity
reweighting and cutoff operations can use the same law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem cavity_gibbs_measure_same_covariance {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (A C : X → ℕ →₀ ℝ)
    (hcov : ∀ x y, cylinderCross (A x) (A y) = cylinderCross (C x) (C y)) :
    gaussianCoordinates.map (fun z => ν.tilted (fun x => H x+cylinderField (A x) z)) =
      gaussianCoordinates.map (fun z => ν.tilted (fun x => H x+cylinderField (C x) z)) := by
  let G := fun w : X → ℝ => ν.tilted (fun x => H x+w x)
  have hm : Measurable (fun p : (X → ℝ) × X => H p.2+p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro x
    exact (measurable_pi_apply x : Measurable (fun w : X → ℝ => w x)).const_add (H x)
  have hG : Measurable G := measurable_random_tilted_measure
    (ν := fun _ : X → ℝ => ν) (H := fun p : (X → ℝ) × X => H p.2+p.1 p.2)
    measurable_const hm
  have hA : Measurable (fun z x => cylinderField (A x) z) :=
    Measurable.of_eval (fun x => measurable_cylinderField (A x))
  have hC : Measurable (fun z x => cylinderField (C x) z) :=
    Measurable.of_eval (fun x => measurable_cylinderField (C x))
  have h := congrArg (fun μ : Measure (X → ℝ) => μ.map G) (cylinder_fields_law_eq A C hcov)
  simpa only [Measure.map_map hG hA, Measure.map_map hG hC, Function.comp_def, G] using h

end InvariantIsing

end

end OAI
