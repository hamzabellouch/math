import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSquareRegularity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialShootingInnerAverage

namespace OAI

/-! The selected inner shooting solution is regular in squared radius at zero. -/

open Set
namespace DefocusingNLS

theorem radialShootingSquare_hasDerivWithinAt_zero (n : ℕ) (w : RadialShootingDisk) :
    HasDerivWithinAt (radialSquareProfile (radialShootingInnerComplex n w))
      (radialComplexSource (n+radialInnerShootingThreshold) (radialShootingA n)
        (radialShootingB w) (radialShootingInnerComplex n w 0)/24) (Ici 0) 0 :=
  radialSquareProfile_hasDerivWithinAt_zero _ _ _ innerBoundaryRadius
    (by linarith [innerBoundaryRadius_bounds.1]) _ (radialShootingInner_differentiable n w)
    (fun r hr => radialShootingInner_derivative_average n w r hr.1 hr.2)

theorem radialShootingSquare_contDiffOn_one (n : ℕ) (w : RadialShootingDisk) :
    ContDiffOn ℝ 1 (radialSquareProfile (radialShootingInnerComplex n w))
      (Icc 0 (innerBoundaryRadius^2)) :=
  radialSquareProfile_contDiffOn_one _ _ _ innerBoundaryRadius
    (by linarith [innerBoundaryRadius_bounds.1]) _ (radialShootingInner_differentiable n w)
    (fun r hr => radialShootingInner_derivative_average n w r hr.1 hr.2)

end DefocusingNLS

end OAI
