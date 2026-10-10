import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingTaylorRemainder
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingEvaluation

namespace OAI

/-! # Pointwise meaning of the uniform expanding-torus linearization -/

namespace DefocusingNLS

/-- At each torus point, the Sobolev derivative is the scalar real derivative. -/
theorem expandingOddPower_fderiv_pointwise (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m : ℕ)
    (q v : FourierL2) (x : SchrodingerTorus) :
    expandingTorusFunction a k L (fderiv ℝ (expandingOddPower a k L ha ha1 hk hL m) q v) x =
      oddPowerDerivative m (expandingTorusFunction a k L q x) (expandingTorusFunction a k L v x) := by
  let E := (expandingPointEvaluation a k L ha ha1 hk hL x).restrictScalars ℝ
  have hE (f : FourierL2) : E f = expandingTorusFunction a k L f x :=
    (expandingTorusFunction_eq_evaluation a k L ha ha1 hk hL x f).symm
  have hN := ((contDiff_expandingOddPower a k L ha ha1 hk hL m).differentiable (by simp) q).hasFDerivAt
  have hleft := E.hasFDerivAt.comp q hN
  have hright := (hasFDerivAt_oddPowerNonlinearity m (E q)).comp q E.hasFDerivAt
  have heq : (fun f : FourierL2 => E (expandingOddPower a k L ha ha1 hk hL m f)) =
      (fun f : FourierL2 => oddPowerNonlinearity m (E f)) := by
    funext f
    simpa only [hE] using expandingOddPower_apply a k L ha ha1 hk hL m f x
  have hderiv : E.comp (fderiv ℝ (expandingOddPower a k L ha ha1 hk hL m) q) =
      (oddPowerDerivative m (E q)).comp E := by
    apply hleft.unique
    simpa only [Function.comp_def, ← heq] using hright
  have h := congrArg (fun L : FourierL2 →L[ℝ] ℂ => L v) hderiv
  simpa only [ContinuousLinearMap.comp_apply, hE] using h

/-- The two circular components of the exact linearized odd-power operator. -/
theorem expandingOddPower_fderiv_pointwise_explicit (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m : ℕ)
    (q v : FourierL2) (x : SchrodingerTorus) :
    expandingTorusFunction a k L (fderiv ℝ (expandingOddPower a k L ha ha1 hk hL m) q v) x =
      ((m + 1 : ℕ) : ℂ) * (expandingTorusFunction a k L q x) ^ m *
        star (expandingTorusFunction a k L q x) ^ m * expandingTorusFunction a k L v x +
      (m : ℂ) * (expandingTorusFunction a k L q x) ^ (m + 1) *
        star (expandingTorusFunction a k L q x) ^ (m - 1) * star (expandingTorusFunction a k L v x) := by
  rw [expandingOddPower_fderiv_pointwise]
  simp [oddPowerDerivative, smul_eq_mul]

/-- The abstract remainder evaluates to the actual scalar nonlinear Taylor remainder. -/
theorem expandingNonlinearRemainder_pointwise (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m : ℕ)
    (q v : FourierL2) (x : SchrodingerTorus) :
    expandingTorusFunction a k L (expandingNonlinearRemainder a k L ha ha1 hk hL m q v) x =
      oddPowerNonlinearity m (expandingTorusFunction a k L q x + expandingTorusFunction a k L v x) -
        oddPowerNonlinearity m (expandingTorusFunction a k L q x) -
          oddPowerDerivative m (expandingTorusFunction a k L q x) (expandingTorusFunction a k L v x) := by
  rw [expandingTorusFunction_eq_evaluation a k L ha ha1 hk hL]
  unfold expandingNonlinearRemainder
  rw [map_sub, map_sub]
  simp only [← expandingTorusFunction_eq_evaluation a k L ha ha1 hk hL, expandingOddPower_apply,
    expandingOddPower_fderiv_pointwise]
  have hadd : expandingTorusFunction a k L (q + v) x =
      expandingTorusFunction a k L q x + expandingTorusFunction a k L v x := by
    simp only [expandingTorusFunction_eq_evaluation a k L ha ha1 hk hL, map_add]
  rw [hadd]

end DefocusingNLS

end OAI
