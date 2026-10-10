import OAI.Probability.SLE.Loewner.InitialTipHeightBound
import OAI.Probability.SLE.Loewner.FutureSlitRadius

namespace OAI

/-! Every point of a mapped future segment lies in a strip whose squared
height is at most twice the exact remaining capacity. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

theorem centeredFutureArc_height_sq_le (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s<t) (ht : t<1) (u : unitInterval) :
    (centeredFutureArc p hi h0 hH hst ht u).im^2≤
      2*(initialCapacity p hi h0 hH t-initialCapacity p hi h0 hH s) := by
  by_cases hu : u=0
  · subst u
    simp only [centeredFutureArc_zero,zero_im,zero_pow two_ne_zero]
    exact mul_nonneg (by norm_num) (sub_nonneg.mpr (initialCapacity_monotone p hi h0 hH hst.le))
  have hv := slitSegmentParameter_le s t hst.le u
  have hh := initialForward_tip_height_bound p hi h0 hH (slitSegmentParameter_gt hst hu)
    (hv.trans_lt ht)
  have he : (centeredFutureArc p hi h0 hH hst ht u).im=
      (initialForwardChart p hi h0 hH s (p (slitSegmentParameter s t hst.le u))).im := by
    change (mappedFutureArc p hi h0 hH hst ht u-(_ : ℂ)).im=_
    rw [sub_im,ofReal_im,sub_zero,mappedFutureArc_segment p hi h0 hH hst ht hu]
  rw [he]
  exact hh.trans (by linarith [initialCapacity_monotone p hi h0 hH hv])

end SLEExactGauge

end

end OAI
