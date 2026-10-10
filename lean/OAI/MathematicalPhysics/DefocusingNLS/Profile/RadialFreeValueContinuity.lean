import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedFreeBoundaryAnalytic

namespace OAI

/-! Continuity of the free value determinant on the physical half-plane. -/

namespace DefocusingNLS
open ProfileCertificate

theorem radialFreeValueDet_continuousAt (ell : ℕ) (z : ProfileMatchingBall)
    (R : ℝ) (hLR : radialShootingR (profileMatchingParameter z) < R)
    (lam : ℂ) (hhalf : -(1/32 : ℝ) ≤ lam.re) :
    ContinuousAt (fun w => spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell
        (radialShootingB (profileMatchingParameter z)) w R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell
        (radialShootingB (profileMatchingParameter z)) w R))) lam := by
  let β := radialShootingB (profileMatchingParameter z)
  have hq (h : ℝ) : -1 < (spectralQ ell h β lam).re := by
    rw [spectralQ_re]
    linarith [Nat.cast_nonneg (α := ℝ) ell]
  have hlog : max 0 (Real.log 4/2) < Real.log R :=
    spectralFreeRadius_log R ((radialShooting_geometry (profileMatchingParameter z)).2.1.trans hLR.le)
  have hp := spectralPhysicalValueMap.continuous.continuousAt.comp
    (spectralFreePositivePhysical_analyticAt ell β lam (hq 1) R hlog.le).differentiableAt.continuousAt
  have hn := spectralPhysicalValueMap.continuous.continuousAt.comp
    (spectralFreeNegativePhysical_analyticAt ell β lam (hq (-1)) R hlog.le).differentiableAt.continuousAt
  exact (hp.fst.mul hn.snd).sub (hp.snd.mul hn.fst)

end DefocusingNLS

end OAI
