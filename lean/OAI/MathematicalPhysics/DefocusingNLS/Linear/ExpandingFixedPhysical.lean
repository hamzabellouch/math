import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalPath
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSobolevNonlinearity
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingBlowupObservation

namespace OAI

/-! # The fixed Sobolev path represents the same normalized torus function -/

open Set

namespace DefocusingNLS

theorem expandingFixedPhysical_value (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (u : C(Icc (0 : ℝ) T, FourierL2)) (t : Icc (0 : ℝ) T) (x : SchrodingerTorus) :
    sobolevTorusFunction k (expandingToSobolev a k ha1 hk
      (expandingPhysicalPath a k L T ha hk hL u t)) x =
      expandingTorusFunction a k (expandingRadius L t) (u t) x := by
  rw [sobolevTorusFunction_expandingToSobolev a k ha ha1 hk]
  change expandingTorusFunction a k 1
    (expandingInverseTransfer a k (expandingRadius L t) ha hk
      (hL.trans (expandingRadius_ge L t hL t.2.1)) (u t)) x = _
  exact DFunLike.congr_fun (expandingInverseTransfer_function a k _ ha ha1 hk _ _) x

end DefocusingNLS

end OAI
