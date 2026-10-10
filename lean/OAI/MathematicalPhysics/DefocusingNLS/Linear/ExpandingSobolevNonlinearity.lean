import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSobolevEquiv
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingNonlinearity
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchrodingerGenerator

namespace OAI

/-! # The fixed-weight identification preserves the actual nonlinearity

Both models represent the same Fourier coefficients.  Consequently the change
of norm intertwines multiplication, conjugation and the Schrödinger generator.
-/

open scoped ComplexConjugate

namespace DefocusingNLS

private theorem coefficient_injective (k : ℝ) :
    Function.Injective (sobolevFourierCoefficient k) := by
  intro f g h
  ext n
  calc
    f n = (sobolevProductWeight k n : ℂ) * sobolevFourierCoefficient k f n :=
      (weight_mul_sobolevFourierCoefficient k f n).symm
    _ = (sobolevProductWeight k n : ℂ) * sobolevFourierCoefficient k g n := by rw [h]
    _ = g n := weight_mul_sobolevFourierCoefficient k g n

theorem expandingToSobolev_product (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f g : FourierL2) :
    expandingToSobolev a k ha1 hk (expandingProduct a k 1 ha ha1 hk le_rfl f g) =
      sobolevProduct k (by linarith) (expandingToSobolev a k ha1 hk f)
        (expandingToSobolev a k ha1 hk g) := by
  apply coefficient_injective k
  funext n
  rw [expandingToSobolev_coefficient, expandingProduct_coefficient,
    sobolevProduct_coefficient]
  unfold expandingProductCoefficient sobolevProductCoefficient
  apply tsum_congr
  intro j
  rw [expandingToSobolev_coefficient, expandingToSobolev_coefficient]

theorem expandingToSobolev_conjugate (a k : ℝ)
    (ha1 : a < 1) (hk : 8 < k) (f : FourierL2) :
    expandingToSobolev a k ha1 hk (fourierConjugate f) =
      fourierConjugate (expandingToSobolev a k ha1 hk f) := by
  apply coefficient_injective k
  funext n
  rw [expandingToSobolev_coefficient, expandingFourierCoefficient_conjugate,
    sobolevFourierCoefficient_conjugate, expandingToSobolev_coefficient]

theorem expandingToSobolev_oddPower (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (f : FourierL2) :
    expandingToSobolev a k ha1 hk (expandingOddPower a k 1 ha ha1 hk le_rfl m f) =
      sobolevOddPower k (by linarith) m (expandingToSobolev a k ha1 hk f) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [expandingOddPower, sobolevOddPower, expandingToSobolev_product,
      expandingToSobolev_conjugate, ih]

theorem expandingToSobolev_lowerInclusion (a k : ℝ)
    (ha1 : a < 1) (hk : 8 < k) (f : FourierL2) :
    expandingToSobolev a k ha1 hk (lowerSobolevInclusion f) =
      lowerSobolevInclusion (expandingToSobolev a k ha1 hk f) := by
  ext n
  simp only [expandingToSobolev_apply, lowerSobolevInclusion_apply]
  ring

theorem expandingToSobolev_lowerGenerator (a k : ℝ)
    (ha1 : a < 1) (hk : 8 < k) (f : FourierL2) :
    expandingToSobolev a k ha1 hk (lowerSobolevGenerator f) =
      lowerSobolevGenerator (expandingToSobolev a k ha1 hk f) := by
  ext n
  simp only [expandingToSobolev_apply, lowerSobolevGenerator_apply]
  ring

theorem sobolevTorusFunction_expandingToSobolev (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : FourierL2)
    (x : SchrodingerTorus) :
    sobolevTorusFunction k (expandingToSobolev a k ha1 hk f) x =
      expandingTorusFunction a k 1 f x := by
  rw [sobolevTorusFunction_eq_tsum k (by linarith),
    expandingTorusFunction_apply a k 1 ha ha1 hk le_rfl]
  apply tsum_congr
  intro n
  rw [expandingToSobolev_coefficient]

end DefocusingNLS

end OAI
