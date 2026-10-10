import OAI.NumberTheory.JointDickman.Arithmetic.PrimeMeasureSupport
import Mathlib.MeasureTheory.Function.JacobianOneDim

namespace OAI

/-! # Restriction and integration for the logarithmic prime limit measure -/
namespace JointDickman
open MeasureTheory Set

 theorem logarithmicPrimeMeasure_restrict_Ioi {c s : ℝ}
    (hc : 0 < c) (hcs : c ≤ s) :
    (logarithmicPrimeMeasure c : Measure ℝ).restrict (Ioi s) =
      (logarithmicPrimeMeasure s : Measure ℝ) := by
  have hs : 0 < s := hc.trans_le hcs
  change (Measure.map Real.exp (volume.restrict (Ioc (Real.log c) 0))).restrict (Ioi s) =
    Measure.map Real.exp (volume.restrict (Ioc (Real.log s) 0))
  rw [Measure.restrict_map Real.measurable_exp measurableSet_Ioi, Measure.restrict_restrict]
  · congr 2
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_Ioi, mem_Ioc, ← Real.log_lt_iff_lt_exp hs]
    constructor
    · rintro ⟨hst, hct, ht⟩
      exact ⟨hst, ht⟩
    · rintro ⟨hst, ht⟩
      exact ⟨hst, (Real.log_le_log hc hcs).trans_lt hst, ht⟩
  · exact Real.measurable_exp measurableSet_Ioi

 theorem logarithmicPrimeMeasure_integral {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (f : ℝ → ℝ) :
    (∫ t, f t ∂(logarithmicPrimeMeasure c : Measure ℝ)) = ∫ t in c..1, f t / t := by
  change (∫ t, f t ∂Measure.map Real.exp (volume.restrict (Ioc (Real.log c) 0))) = _
  rw [Real.isOpenEmbedding_exp.measurableEmbedding.integral_map]
  rw [intervalIntegral.integral_of_le hc1]
  have hj := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
    (fun t (_ : t ∈ Ioc (Real.log c) 0) => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    Real.exp_injective.injOn (fun t => f t / t)
  rw [Real.image_exp_Ioc, Real.exp_log hc, Real.exp_zero] at hj
  rw [hj]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [abs_of_pos (Real.exp_pos t), smul_eq_mul]
  field_simp

end JointDickman

end OAI
