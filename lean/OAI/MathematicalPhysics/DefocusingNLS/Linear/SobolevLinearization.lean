import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevTaylorRemainder

namespace OAI

/-! # Pointwise meaning of the Sobolev linearization

Bounded torus observation commutes with the real Fréchet derivative.  Thus
the operator used in the perturbation equation is exactly the scalar
linearization, including its conjugate component.
-/

namespace DefocusingNLS

/-- At each torus point, the Sobolev derivative is the scalar real derivative. -/
theorem sobolevOddPower_fderiv_pointwise (k : ℝ) (hk : 6 < k) (m : ℕ)
    (q v : FourierL2) (x : SchrodingerTorus) :
    sobolevTorusFunction k (fderiv ℝ (sobolevOddPower k hk m) q v) x =
      oddPowerDerivative m (sobolevTorusFunction k q x) (sobolevTorusFunction k v x) := by
  let E := (sobolevPointEvaluation k hk x).restrictScalars ℝ
  have hE (f : FourierL2) : E f = sobolevTorusFunction k f x :=
    (sobolevTorusFunction_apply k hk x f).symm
  have hN := ((contDiff_sobolevOddPower k hk m).differentiable (by simp) q).hasFDerivAt
  have hleft := E.hasFDerivAt.comp q hN
  have hright := (hasFDerivAt_oddPowerNonlinearity m (E q)).comp q E.hasFDerivAt
  have heq : (fun f : FourierL2 => E (sobolevOddPower k hk m f)) =
      (fun f : FourierL2 => oddPowerNonlinearity m (E f)) := by
    funext f
    simpa only [hE] using sobolevOddPower_apply k hk m f x
  have hderiv : E.comp (fderiv ℝ (sobolevOddPower k hk m) q) =
      (oddPowerDerivative m (E q)).comp E := by
    apply hleft.unique
    simpa only [Function.comp_def, ← heq] using hright
  have h := congrArg (fun L : FourierL2 →L[ℝ] ℂ => L v) hderiv
  simpa only [ContinuousLinearMap.comp_apply, hE] using h

/-- The two circular components of the exact linearized odd-power operator. -/
theorem sobolevOddPower_fderiv_pointwise_explicit (k : ℝ) (hk : 6 < k) (m : ℕ)
    (q v : FourierL2) (x : SchrodingerTorus) :
    sobolevTorusFunction k (fderiv ℝ (sobolevOddPower k hk m) q v) x =
      ((m + 1 : ℕ) : ℂ) * (sobolevTorusFunction k q x) ^ m *
        star (sobolevTorusFunction k q x) ^ m * sobolevTorusFunction k v x +
      (m : ℂ) * (sobolevTorusFunction k q x) ^ (m + 1) *
        star (sobolevTorusFunction k q x) ^ (m - 1) * star (sobolevTorusFunction k v x) := by
  rw [sobolevOddPower_fderiv_pointwise]
  simp [oddPowerDerivative, smul_eq_mul]

/-- The abstract remainder evaluates to the actual scalar nonlinear Taylor remainder. -/
theorem sobolevNonlinearRemainder_pointwise (k : ℝ) (hk : 6 < k) (m : ℕ)
    (q v : FourierL2) (x : SchrodingerTorus) :
    sobolevTorusFunction k (sobolevNonlinearRemainder k hk m q v) x =
      oddPowerNonlinearity m (sobolevTorusFunction k q x + sobolevTorusFunction k v x) -
        oddPowerNonlinearity m (sobolevTorusFunction k q x) -
          oddPowerDerivative m (sobolevTorusFunction k q x) (sobolevTorusFunction k v x) := by
  rw [sobolevTorusFunction_apply k hk]
  unfold sobolevNonlinearRemainder
  rw [map_sub, map_sub]
  simp only [← sobolevTorusFunction_apply k hk, sobolevOddPower_apply,
    sobolevOddPower_fderiv_pointwise]
  have hadd : sobolevTorusFunction k (q + v) x =
      sobolevTorusFunction k q x + sobolevTorusFunction k v x := by
    simp only [sobolevTorusFunction_apply k hk, map_add]
  rw [hadd]

end DefocusingNLS

end OAI
