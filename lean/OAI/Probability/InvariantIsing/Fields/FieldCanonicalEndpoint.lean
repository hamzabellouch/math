import OAI.Probability.InvariantIsing.Magnetic.MagneticCanonicalSpin

namespace OAI

/-! The one-site canonical endpoint law and its final spin draw. The
ordinary root Gaussian is retained explicitly. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldTailEndpointKernel : (L : List (ℝ × ℝ≥0)) →
    (∀ av ∈ L, 0 < av.1) → Kernel ℝ ℝ
  | [], _ => Kernel.id
  | av :: L, hL =>
    let ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    fieldTailEndpointKernel L ht ∘ₖ
      fieldTransitionKernel av.1 av.2
        (fieldScalarValue L (fun z => Real.log (Real.cosh z))) hreg.1

instance fieldTailEndpointKernel_markov (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) : IsMarkovKernel (fieldTailEndpointKernel L hL) := by
  induction L with
  | nil => change IsMarkovKernel Kernel.id; infer_instance
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let _ := ih ht
    change IsMarkovKernel (_ ∘ₖ _)
    infer_instance

lemma fieldTailSpinKernel_endpoint (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) :
    fieldTailSpinKernel L hL = scalarSpinKernel ∘ₖ fieldTailEndpointKernel L hL := by
  induction L with
  | nil => simp [fieldTailSpinKernel, fieldTailEndpointKernel]
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    change fieldTailSpinKernel L ht ∘ₖ _ = scalarSpinKernel ∘ₖ (fieldTailEndpointKernel L ht ∘ₖ _)
    rw [ih ht, Kernel.comp_assoc]

def fieldCanonicalEndpointLaw (h : FieldStep) (b : ℝ) : Measure ℝ :=
  fieldTailEndpointKernel (scalarFieldIncrements h) (scalarFieldIncrements_positive h) ∘ₘ
    gaussianReal b (NNReal.mk (h.height 0) (h.nonneg 0))

instance fieldCanonicalEndpointLaw_probability (h : FieldStep) (b : ℝ) :
    IsProbabilityMeasure (fieldCanonicalEndpointLaw h b) := by
  unfold fieldCanonicalEndpointLaw
  infer_instance

lemma fieldTransitionKernel_zero (v : ℝ≥0) (F : ℝ → ℝ) (hF : Measurable F)
    (hG : HasLinearGrowth F) (z : ℝ) :
    fieldTransitionKernel 0 v F hF z = gaussianReal z v := by
  rw [fieldTransitionKernel_eq_tilted 0 v F hF hG]
  simp

theorem fieldCanonicalSpinLaw_endpoint (h : FieldStep) (b : ℝ) :
    fieldCanonicalSpinLaw h b = scalarSpinKernel ∘ₘ fieldCanonicalEndpointLaw h b := by
  have hreg := fieldScalarValue_regular (scalarFieldIncrements h)
    (scalarFieldIncrements_positive h) measurable_logCosh logCosh_linearGrowth
  rw [fieldCanonicalEndpointLaw, Measure.comp_assoc, ← fieldTailSpinKernel_endpoint]
  rw [fieldCanonicalSpinLaw, Kernel.comp_apply, fieldTransitionKernel_zero _ _ hreg.1 hreg.2]

end InvariantIsing

end

end OAI
