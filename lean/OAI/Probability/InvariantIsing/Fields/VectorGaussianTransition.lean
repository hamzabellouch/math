import OAI.Probability.InvariantIsing.Magnetic.RestrictedFieldFactorization
import OAI.Probability.InvariantIsing.Core.TiltedRelativeEntropy

namespace OAI

/-! The actual vector Gaussian transition for a nonseparable terminal,
including constrained spin blocks. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal BigOperators

namespace InvariantIsing

def vectorShiftGaussianKernel (N : ℕ) (v : ℝ≥0) : Kernel (Fin N → ℝ) (Fin N → ℝ) :=
  fieldVectorTransitionKernel N 0 v (fun _ => 0) measurable_const

instance vectorShiftGaussianKernel_markov (N : ℕ) (v : ℝ≥0) :
    IsMarkovKernel (vectorShiftGaussianKernel N v) := by
  unfold vectorShiftGaussianKernel
  infer_instance

lemma vectorShiftGaussianKernel_apply (N : ℕ) (v : ℝ≥0) (z : Fin N → ℝ) :
    vectorShiftGaussianKernel N v z = Measure.pi (fun i => gaussianReal (z i) v) := by
  have hg : HasLinearGrowth (fun _ : ℝ => (0 : ℝ)) :=
    ⟨0, 0, le_rfl, le_rfl, fun _ => by simp⟩
  rw [vectorShiftGaussianKernel, fieldVectorTransitionKernel_eq_tilted 0 v _ measurable_const hg]
  simp

def vectorGaussianTransition (N : ℕ) (a : ℝ) (v : ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) : Kernel (Fin N → ℝ) (Fin N → ℝ) := by
  have hW : Measurable (fun y : Fin N → ℝ => ENNReal.ofReal (Real.exp (a * F y))) :=
    (hF.const_mul a).exp.ennreal_ofReal
  have hm := measurable_normalizeMass.comp
    ((measurable_withDensity_fixed hW).comp (vectorShiftGaussianKernel N v).measurable)
  exact ⟨fun z => normalizeMass ((vectorShiftGaussianKernel N v z).withDensity
    (fun y => ENNReal.ofReal (Real.exp (a * F y)))), hm⟩

instance vectorGaussianTransition_markov (N : ℕ) (a : ℝ) (v : ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) :
    IsMarkovKernel (vectorGaussianTransition N a v F hF) :=
  ⟨fun _ => normalizeMass_probability _⟩

lemma vectorGaussian_shift_exp_integrable {N : ℕ} (hN : 0 < N) (a : ℝ) (v : ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : Fin N → ℝ) :
    Integrable (fun y => Real.exp (a * F y)) (Measure.pi (fun i => gaussianReal (z i) v)) := by
  rw [← (vectorGaussian_shift v z).map_eq]
  apply (integrable_map_measure (hF.const_mul a).exp.aestronglyMeasurable
    (show AEMeasurable (fun w : Fin N → ℝ => z + w) (vectorGaussianLaw N v : Measure (Fin N → ℝ)) from
      (measurable_const.add measurable_id).aemeasurable)).mpr
  exact integrable_exp_of_linearGrowth _ (vectorGaussianLaw_moments hN v)
    (hF.comp (measurable_const.add measurable_id)) (hG.add_left z) a

lemma vectorGaussianTransition_eq_tilted {N : ℕ} (hN : 0 < N) (a : ℝ) (v : ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : Fin N → ℝ) :
    vectorGaussianTransition N a v F hF z =
      (Measure.pi (fun i => gaussianReal (z i) v)).tilted (fun y => a * F y) := by
  change normalizeMass ((vectorShiftGaussianKernel N v z).withDensity _) = _
  rw [vectorShiftGaussianKernel_apply]
  exact normalizeMass_exp _ _ (hF.const_mul a)
    (vectorGaussian_shift_exp_integrable hN a v F hF hG z)

lemma vectorGaussianTransition_eq_map {N : ℕ} (hN : 0 < N) (a : ℝ) (v : ℝ≥0)
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : Fin N → ℝ) :
    vectorGaussianTransition N a v F hF z =
      ((vectorGaussianLaw N v : Measure (Fin N → ℝ)).tilted
        (fun w => a * F (z + w))).map (fun w => z + w) := by
  rw [vectorGaussianTransition_eq_tilted hN a v F hF hG z]
  have he := cavity_tilt_map (vectorGaussianLaw N v : Measure (Fin N → ℝ))
    (fun w => z + w) (measurable_const.add measurable_id) (fun y => a * F y) (hF.const_mul a)
  rw [(vectorGaussian_shift v z).map_eq] at he
  exact he.symm

end InvariantIsing

end

end OAI
