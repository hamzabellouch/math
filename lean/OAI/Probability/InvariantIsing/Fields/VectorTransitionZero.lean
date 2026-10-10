import OAI.Probability.InvariantIsing.Fields.VectorGaussianTransition

namespace OAI

/-! A zero-variance constrained Gaussian transition fixes the current field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma vectorGaussianTransition_zero {N : ℕ} (hN : 0 < N) (a : ℝ)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : Fin N → ℝ) :
    vectorGaussianTransition N a 0 F hF z = Measure.dirac z := by
  rw [vectorGaussianTransition_eq_tilted hN a 0 F hF hG z]
  have hd := fieldVectorTailEndpointKernel_product N [] (by simp) z
  change Measure.dirac z = Measure.pi (fun i => Measure.dirac (z i)) at hd
  simp_rw [gaussianReal_zero_var]
  rw [← hd]
  have he := cavity_tilt_map (Measure.dirac ()) (fun _ : Unit => z) measurable_const
    (fun y => a * F y) (hF.const_mul a)
  simpa only [Function.comp_def, tilted_const, Measure.map_dirac' measurable_const] using he.symm

end InvariantIsing

end

end OAI
