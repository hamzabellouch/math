import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.CoulombEvaluationProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.ComputableHopping
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibrationSquareError

namespace OAI

/-! The literal scalar function supplied to calibrated-distance bisection.
The displacement/weight bound, amplification and requested accuracy are unary;
the positive target parameters and the queried distance are rational. -/

namespace ContinuumCoulomb.CalibratedEvaluation

abbrev Environment := (ℕ × ℕ) × (ℕ × (ℚ × ℚ))

noncomputable def coulombPrecision (N P : ℕ) : ℕ := 64 * (N + 1) * (P + 1) ^ 2
noncomputable def hoppingPrecision (scale P : ℕ) : ℕ := 4 * (scale + 1) * (P + 1)
noncomputable def rootPrecision (P : ℕ) : ℕ := 8 * (P + 1)

noncomputable def gap (rho N P : ℕ) (d : ℚ) : ℚ :=
  max 0 (CoulombEvaluation.approximate rho (coulombPrecision N P) 0 -
    CoulombEvaluation.approximate rho (coulombPrecision N P) d)

noncomputable def root (rho N P : ℕ) (K d : ℚ) : ℚ :=
  RationalSquareRoot.value (rootPrecision P, K * gap rho N P d)

noncomputable def value (rho : ℕ) (e : Environment) (d : ℚ) : ℚ :=
  (e.2.1 : ℚ) * ComputableHopping.approximate
      ((e.1.1, hoppingPrecision e.2.1 e.1.2), d) -
    e.2.2.1 * root rho e.1.1 e.1.2 e.2.2.2 d

end ContinuumCoulomb.CalibratedEvaluation

end OAI
