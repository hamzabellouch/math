import OAI.Probability.InvariantIsing.Gaussian.GordonSlopeSign

namespace OAI

/-! Differentiation under the finite Gaussian minimum--maximum interpolation. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

def gordonCurveMean {d : ℕ} (C A : U × V → Fin d → ℝ) (t : ℝ) : ℝ :=
  ∫ g, gordonValue (fun x => linearGaussian (cavityGaussianCurve C A t) g x)
    ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)

def gordonCurveSlope {d : ℕ} (C A : U × V → Fin d → ℝ) (t : ℝ) : ℝ :=
  ∫ g, gordonMean (fun x => linearGaussian (cavityGaussianCurve C A t) g x)
    (fun x => linearGaussian (cavityGaussianCurveDerivative C A t) g x)
    ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)

lemma gordonCurveMean_hasDerivAt {d : ℕ} (C A : U × V → Fin d → ℝ) (t : ℝ) :
    HasDerivAt (gordonCurveMean C A) (gordonCurveSlope C A t) t := by
  let μ := Measure.pi (fun _ : Fin d => gaussianReal 0 1)
  let B := fun g : Fin d → ℝ => ∑ x, (|linearGaussian C g x|+|linearGaussian A g x|)
  have hm (s : ℝ) : AEStronglyMeasurable (fun g =>
      gordonValue (fun x => linearGaussian (cavityGaussianCurve C A s) g x)) μ :=
    (continuous_gordonValue _ (fun x => by unfold linearGaussian; fun_prop)).aestronglyMeasurable
  have hi : Integrable (fun g =>
      gordonValue (fun x => linearGaussian (cavityGaussianCurve C A t) g x)) μ := by
    simpa only [zero_add] using integrable_gordonValue (fun _ => 0) (cavityGaussianCurve C A t)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (s := Set.univ)
    (F' := fun s g => gordonMean (fun x => linearGaussian (cavityGaussianCurve C A s) g x)
      (fun x => linearGaussian (cavityGaussianCurveDerivative C A s) g x))
    (bound := B) Filter.univ_mem (Filter.Eventually.of_forall hm) hi ?_ ?_ ?_ ?_).2
  · exact (continuous_gordonMean _ _
      (fun x => by unfold linearGaussian; fun_prop)
      (fun x => by unfold linearGaussian; fun_prop)).aestronglyMeasurable
  · apply ae_of_all
    intro g s _
    rw [Real.norm_eq_abs]
    apply gordonMean_bound
    intro x
    exact (cavityGaussianCurveDerivative_bound C A s g x).trans
      (Finset.single_le_sum
        (f := fun x => |linearGaussian C g x|+|linearGaussian A g x|)
        (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
        (Finset.mem_univ x))
  · exact integrable_finsetSum _ (fun x _ =>
      (integrable_linearGaussian C x).abs.add (integrable_linearGaussian A x).abs)
  · apply ae_of_all
    intro g s _
    exact gordonValue_hasDerivAt (fun x => cavityGaussianCurve_hasDerivAt C A s g x)

end InvariantIsing

end

end OAI
