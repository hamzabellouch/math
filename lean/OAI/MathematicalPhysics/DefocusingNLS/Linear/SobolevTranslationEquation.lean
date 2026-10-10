import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevTranslation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchrodingerNonlinearEquation

namespace OAI

/-! # Translation covariance of the strong nonlinear Schrödinger equation -/

open scoped ComplexConjugate

namespace DefocusingNLS

theorem sobolevFourierCoefficient_translation (k : ℝ) (x : SchrodingerTorus)
    (f : FourierL2) (n : frequencyLattice) :
    sobolevFourierCoefficient k (sobolevTranslation x f) n =
      torusCharacter n x * sobolevFourierCoefficient k f n := by
  simp only [sobolevFourierCoefficient, sobolevTranslation_apply, Algebra.smul_def]
  ring

theorem sobolevProduct_translation (k : ℝ) (hk : 6 < k) (x : SchrodingerTorus)
    (f g : FourierL2) :
    sobolevProduct k hk (sobolevTranslation x f) (sobolevTranslation x g) =
      sobolevTranslation x (sobolevProduct k hk f g) := by
  ext n
  change (sobolevProductWeight k n : ℂ) *
      (∑' j, sobolevFourierCoefficient k (sobolevTranslation x f) j *
        sobolevFourierCoefficient k (sobolevTranslation x g) (n - j)) =
    torusCharacter n x * ((sobolevProductWeight k n : ℂ) *
      ∑' j, sobolevFourierCoefficient k f j * sobolevFourierCoefficient k g (n - j))
  simp only [sobolevFourierCoefficient_translation]
  have heq (j : frequencyLattice) :
      (torusCharacter j x * sobolevFourierCoefficient k f j) *
        (torusCharacter (n - j) x * sobolevFourierCoefficient k g (n - j)) =
      torusCharacter n x * (sobolevFourierCoefficient k f j *
        sobolevFourierCoefficient k g (n - j)) := by
    have hchar : torusCharacter j x * torusCharacter (n - j) x = torusCharacter n x := by
      rw [← torusCharacter_frequency_add, add_sub_cancel]
    calc
      _ = (torusCharacter j x * torusCharacter (n - j) x) *
        (sobolevFourierCoefficient k f j * sobolevFourierCoefficient k g (n - j)) := by ring
      _ = _ := by rw [hchar]
  simp_rw [heq]
  rw [tsum_mul_left]
  ring

theorem fourierConjugate_translation (x : SchrodingerTorus) (f : FourierL2) :
    fourierConjugate (sobolevTranslation x f) = sobolevTranslation x (fourierConjugate f) := by
  ext n
  simp [torusCharacter_neg]

/-- Translation commutes with the actual polynomial Sobolev nonlinearity. -/
theorem sobolevOddPower_translation (k : ℝ) (hk : 6 < k) (m : ℕ)
    (x : SchrodingerTorus) (f : FourierL2) :
    sobolevOddPower k hk m (sobolevTranslation x f) =
      sobolevTranslation x (sobolevOddPower k hk m f) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [sobolevOddPower, ih, fourierConjugate_translation, sobolevProduct_translation]

theorem lowerSobolevInclusion_translation (x : SchrodingerTorus) (f : FourierL2) :
    lowerSobolevInclusion (sobolevTranslation x f) =
      sobolevTranslation x (lowerSobolevInclusion f) := by
  ext n
  simp only [lowerSobolevInclusion_apply, sobolevTranslation_apply]
  ring

theorem lowerSobolevGenerator_translation (x : SchrodingerTorus) (f : FourierL2) :
    lowerSobolevGenerator (sobolevTranslation x f) =
      sobolevTranslation x (lowerSobolevGenerator f) := by
  ext n
  simp only [lowerSobolevGenerator_apply, sobolevTranslation_apply]
  ring

theorem schrodingerFlow_translation (t : ℝ) (x : SchrodingerTorus) (f : FourierL2) :
    schrodingerFlow t (sobolevTranslation x f) =
      sobolevTranslation x (schrodingerFlow t f) := by
  ext n
  simp only [schrodingerFlow_apply, sobolevTranslation_apply]
  ring

/-- Spatially translated strong solutions satisfy the same defocusing equation. -/
theorem hasDerivAt_sobolevSchrodinger_translation
    (k : ℝ) (hk : 6 < k) (m : ℕ) (x : SchrodingerTorus) (u : ℝ → FourierL2) (t : ℝ)
    (hu : HasDerivAt (fun s => lowerSobolevInclusion (u s))
      (lowerSobolevGenerator (u t) -
        Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (u t))) t) :
    HasDerivAt (fun s => lowerSobolevInclusion (sobolevTranslation x (u s)))
      (lowerSobolevGenerator (sobolevTranslation x (u t)) -
        Complex.I • lowerSobolevInclusion
          (sobolevOddPower k hk m (sobolevTranslation x (u t)))) t := by
  let T := (sobolevTranslation x).toContinuousLinearMap.restrictScalars ℝ
  have h := T.hasFDerivAt.comp_hasDerivAt t hu
  change HasDerivAt (fun s => sobolevTranslation x (lowerSobolevInclusion (u s)))
    (sobolevTranslation x (lowerSobolevGenerator (u t) -
      Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (u t)))) t at h
  simpa only [Function.comp_def, lowerSobolevInclusion_translation,
    lowerSobolevGenerator_translation, sobolevOddPower_translation, map_sub, map_smul] using h

end DefocusingNLS

end OAI
