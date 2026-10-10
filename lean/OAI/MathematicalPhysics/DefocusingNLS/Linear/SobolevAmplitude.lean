import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevPhase

namespace OAI

/-! # Scalar amplitude covariance of the Sobolev nonlinearity

This exact scaling identity supplies the amplitude factor in the passage from
similarity time to physical Schrödinger time.
-/

open scoped ComplexConjugate

namespace DefocusingNLS

theorem sobolevOddPower_smul (k : ℝ) (hk : 6 < k) (m : ℕ)
    (c : ℂ) (f : FourierL2) :
    sobolevOddPower k hk m (c • f) =
      ((c * conj c) ^ m * c) • sobolevOddPower k hk m f := by
  induction m with
  | zero => simp [sobolevOddPower]
  | succ m ih =>
    simp only [sobolevOddPower, ih, fourierConjugate_smul,
      sobolevProduct_smul_left, sobolevProduct_smul_right, smul_smul]
    congr 1
    rw [pow_succ]
    ring

theorem sobolevOddPower_smul_norm (k : ℝ) (hk : 6 < k) (m : ℕ)
    (c : ℂ) (f : FourierL2) :
    sobolevOddPower k hk m (c • f) =
      ((‖c‖ ^ (2 * m) : ℝ) : ℂ) • (c • sobolevOddPower k hk m f) := by
  rw [sobolevOddPower_smul, smul_smul, Complex.mul_conj, ← Complex.sq_norm]
  congr 1
  rw [← Complex.ofReal_pow, ← pow_mul]

end DefocusingNLS

end OAI
