import OAI.Analysis.CircleDomains.Transfer.SourceAnchor

namespace OAI

/-! A plane homeomorphism carrying one boundary circle onto another carries
its bounded closed disk onto the corresponding bounded closed disk. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

lemma homeomorph_image_closedBall_of_sphere (F : ℂ ≃ₜ ℂ) {c a : ℂ} {r s : ℝ}
    (hr : 0<r) (hs : 0<s) (hf : F '' sphere c r=sphere a s) :
    F '' closedBall c r=closedBall a s := by
  have hb : F '' ball c r=ball a s := by
    rw [←roundJordanAt_interior a s hs]
    apply open_eq_jordanInterior_of_frontier _ (F.isOpenMap _ isOpen_ball)
      (((isCompact_closedBall c r).image F.continuous).isBounded.subset
        (image_mono ball_subset_closedBall))
      ((nonempty_ball.mpr hr).image F)
    rw [←F.image_frontier,frontier_ball _ hr.ne',hf,roundJordanAt_interior,
        frontier_ball _ hs.ne']
  rw [←closure_ball c hr.ne',F.image_closure,hb,closure_ball a hs.ne']

end CircleDomainRigidity

end

end OAI
