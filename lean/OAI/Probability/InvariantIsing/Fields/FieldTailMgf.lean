import OAI.Probability.InvariantIsing.Core.KernelExponentialBound
import OAI.Probability.InvariantIsing.Fields.FieldIncrementMgf

namespace OAI

/-! Canonical endpoint exponential moments depend only on the sum of
increment variances. Arbitrarily small positive exponents and arbitrarily
many levels are allowed. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldTailVariance (L : List (ℝ × ℝ≥0)) : ℝ :=
  (L.map (fun av => (av.2 : ℝ))).sum

lemma fieldTransitionKernel_integrable_exp (v : ℝ≥0) (z b t : ℝ)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) :
    Integrable (fun y => Real.exp (t * y)) (fieldTransitionKernel b v F hF z) := by
  rw [fieldTransitionKernel_eq_tilted b v F hF hG]
  apply integrable_exp_of_linearGrowth _
    (exponentialNormMoments_tilted (gaussianReal z v)
      (gaussianReal_exponentialNormMoments z v) F hF hG b) measurable_id
  refine ⟨0, 1, le_rfl, zero_le_one, ?_⟩
  intro x
  simp [Real.norm_eq_abs]

theorem fieldTailEndpointKernel_mgf (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hB : ∀ av ∈ L, av.1 ≤ 1) (t z : ℝ) :
    Integrable (fun y => Real.exp (t * y)) (fieldTailEndpointKernel L hL z) ∧
      (∫ y, Real.exp (t * y) ∂fieldTailEndpointKernel L hL z) ≤
        Real.exp (t * z + (t ^ 2 / 2 + |t|) * fieldTailVariance L) := by
  induction L generalizing z with
  | nil =>
    constructor
    · change Integrable (fun y => Real.exp (t * y)) (Measure.dirac z)
      exact integrable_dirac (by simp)
    · simp [fieldTailEndpointKernel, Kernel.id_apply, fieldTailVariance]
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hBt := fun bv hb => hB bv (List.mem_cons_of_mem av hb)
    have hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    have hκ (x : ℝ) := And.intro
      (fieldTransitionKernel_integrable_exp av.2 x av.1 t _ hreg.1 hreg.2)
      (fieldScalarTransition_mgf L ht av.2 x av.1 t
        (hL av (List.mem_cons_self)).le (hB av (List.mem_cons_self)))
    have he := kernel_exp_bound_comp
      (fieldTransitionKernel av.1 av.2 (fieldScalarValue L (fun y => Real.log (Real.cosh y))) hreg.1)
      (fieldTailEndpointKernel L ht) t ((t ^ 2 / 2 + |t|) * av.2)
      ((t ^ 2 / 2 + |t|) * fieldTailVariance L) hκ (ih ht hBt) z
    refine ⟨he.1, he.2.trans_eq ?_⟩
    congr 1
    simp only [fieldTailVariance, List.map_cons, List.sum_cons]
    ring

end InvariantIsing

end

end OAI
