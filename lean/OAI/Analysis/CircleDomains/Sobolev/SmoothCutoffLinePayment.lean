import OAI.Analysis.CircleDomains.Rigidity.TraceBalloonCutoff
import OAI.Analysis.CircleDomains.Sobolev.PhysicalCoordinateLines

namespace OAI

/-! The smooth balloon derivative bound pays for all line increments,
including segments crossing components on which the raw scalar jumps. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem smooth_line_increment_payment {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) {x y : ℝ}
    (hg : IntervalIntegrable g volume x y)
    (hb : ∀ t ∈ uIcc x y, |deriv f t| ≤ g t) :
    |f x-f y| ≤ ∫ t in uIoc x y, g t := by
  have hi : IntervalIntegrable (deriv f) volume x y :=
    hf.continuous_deriv_one.intervalIntegrable x y
  have he := intervalIntegral.integral_deriv_eq_sub
    (fun z (_ : z ∈ uIcc y x) => hf.differentiable_one z) hi.symm
  rw [← he,← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
  rw [uIoc_comm y x]
  apply integral_mono_ae hi.norm.def' hg.def'
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  exact hb t (uIoc_subset_uIcc ht)

end CircleDomainRigidity

end

end OAI
