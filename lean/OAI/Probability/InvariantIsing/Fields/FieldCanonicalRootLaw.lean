import OAI.Probability.InvariantIsing.Fields.FieldEndpointIntegrability
import OAI.Probability.InvariantIsing.Fields.FieldCanonicalVectorMoments

namespace OAI

/-! The biased Gaussian root followed by the full canonical recursion
has exactly the product endpoint law used in the terminal estimate. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

theorem fieldCanonicalVectorLaw_root (N : ℕ) (h : FieldStep) (b : Fin N → ℝ) :
    fieldVectorTailEndpointKernel N (scalarFieldIncrements h) (scalarFieldIncrements_positive h) ∘ₘ
      Measure.pi (fun i => gaussianReal (b i) (NNReal.mk (h.height 0) (h.nonneg 0))) =
        fieldCanonicalVectorLaw N h b := by
  rw [product_kernel_comp (fieldTailEndpointKernel (scalarFieldIncrements h)
    (scalarFieldIncrements_positive h)) _
    (fieldVectorTailEndpointKernel_product N _ _)]
  rfl

lemma fieldCanonicalEndpointLaw_integrable_id (h : FieldStep) (b : ℝ) :
    Integrable (fun y : ℝ => y) (fieldCanonicalEndpointLaw h b) := by
  have hp := (fieldCanonicalEndpointLaw_mgf h b 1).1
  have hn := (fieldCanonicalEndpointLaw_mgf h b (-1)).1
  apply (hp.add hn).mono' measurable_id.aestronglyMeasurable
  apply ae_of_all
  intro y
  rw [Real.norm_eq_abs]
  simp only [one_mul, neg_one_mul, Pi.add_apply, id_eq]
  by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg hy]
    linarith [Real.add_one_le_exp y, Real.exp_pos (-y)]
  · rw [abs_of_nonpos (le_of_not_ge hy)]
    linarith [Real.add_one_le_exp (-y), Real.exp_pos y]

lemma fieldCanonicalVectorLaw_linear_integrable (N : ℕ) (h : FieldStep) (b : Fin N → ℝ)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) :
    Integrable F (fieldCanonicalVectorLaw N h b) :=
  integrable_linearGrowth_pi _ (fun i => fieldCanonicalEndpointLaw_integrable_id h (b i)) F hF hG

end InvariantIsing

end

end OAI
