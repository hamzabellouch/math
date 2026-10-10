import OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicMeasureCalculus

namespace OAI

/-! # Integrability under the logarithmic change of variables -/
namespace JointDickman
open MeasureTheory Set

 theorem logarithmicPrimeMeasure_integrable_iff {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (f : ℝ → ℝ) :
    Integrable f (logarithmicPrimeMeasure c : Measure ℝ) ↔
      IntervalIntegrable (fun t => f t / t) volume c 1 := by
  change Integrable f (Measure.map Real.exp (volume.restrict (Ioc (Real.log c) 0))) ↔ _
  rw [Real.isOpenEmbedding_exp.measurableEmbedding.integrable_map_iff,
    intervalIntegrable_iff_integrableOn_Ioc_of_le hc1]
  have hj := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioc
    (fun t (_ : t ∈ Ioc (Real.log c) 0) => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    Real.exp_injective.injOn (fun t => f t / t)
  rw [Real.image_exp_Ioc, Real.exp_log hc, Real.exp_zero] at hj
  rw [hj]
  unfold IntegrableOn
  have he : (fun x : ℝ => |Real.exp x| • (f (Real.exp x) / Real.exp x)) = f ∘ Real.exp := by
    funext t
    simp only [Function.comp_apply, abs_of_pos (Real.exp_pos t), smul_eq_mul]
    field_simp
  rw [he]

end JointDickman

end OAI
