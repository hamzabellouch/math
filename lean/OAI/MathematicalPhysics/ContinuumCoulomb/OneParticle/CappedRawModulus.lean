import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.RawDensityModulus

namespace OAI

/-! A polynomial modulus for the actual six-coordinate capped density
integrand. Relative displacement has no effect on this modulus. -/

noncomputable section
namespace ContinuumCoulomb

theorem bounded_product_sub {a b c d : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    |a * b - c * d| ≤ |a - c| + |b - d| := by
  have he : a * b - c * d = a * (b - d) + (a - c) * d := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hd0]
  have h1 := mul_le_of_le_one_left (abs_nonneg (b - d)) ha1
  have h2 := mul_le_of_le_one_right (abs_nonneg (a - c)) hd1
  linarith

theorem cappedRawPair_modulus {freq ε L : ℝ} (hf : 0 ≤ freq) (hε : 0 < ε)
    (shift : Position) (x y x' y' : Position)
    (hx : |(positionSplitCoordinates x).2| ≤ L)
    (hy : |(positionSplitCoordinates y).2| ≤ L)
    (hx' : |(positionSplitCoordinates x').2| ≤ L)
    (hy' : |(positionSplitCoordinates y').2| ≤ L) :
    |cappedPairIntegrand ε shift (localizedRawDensity freq) (localizedRawDensity freq) (x, y) -
      cappedPairIntegrand ε shift (localizedRawDensity freq) (localizedRawDensity freq) (x', y')| ≤
      ((64 + 2 * freq * L) * ε⁻¹ + ε⁻¹ ^ 2) * (‖x - x'‖ + ‖y - y'‖) := by
  let a := localizedRawDensity freq x * localizedRawDensity freq y
  let b := localizedRawDensity freq x' * localizedRawDensity freq y'
  let k := cappedCoulombKernel ε (x - y - shift)
  let k' := cappedCoulombKernel ε (x' - y' - shift)
  have hb0 : 0 ≤ b := mul_nonneg (localizedRawDensity_nonnegative _ _) (localizedRawDensity_nonnegative _ _)
  have hb1 : b ≤ 1 := (mul_le_mul (localizedRawDensity_le_one hf _)
    (localizedRawDensity_le_one hf _) (localizedRawDensity_nonnegative _ _) zero_le_one).trans_eq (one_mul 1)
  have hk0 : 0 ≤ k := cappedCoulombKernel_nonnegative hε _
  have hk1 : k ≤ ε⁻¹ := cappedCoulombKernel_le hε _
  have hab : |a - b| ≤ (64 + 2 * freq * L) * (‖x - x'‖ + ‖y - y'‖) := by
    have h := bounded_product_sub (a := localizedRawDensity freq x)
      (b := localizedRawDensity freq y) (c := localizedRawDensity freq x')
      (d := localizedRawDensity freq y') (localizedRawDensity_nonnegative freq x)
      (localizedRawDensity_le_one hf x) (localizedRawDensity_nonnegative freq y')
      (localizedRawDensity_le_one hf y')
    apply h.trans
    have h1 := localizedRawDensity_box_modulus hf x x' hx hx'
    have h2 := localizedRawDensity_box_modulus hf y y' hy hy'
    linarith
  have hkk : |k - k'| ≤ ε⁻¹ ^ 2 * (‖x - x'‖ + ‖y - y'‖) := by
    have h := cappedCoulombKernel_norm_sub hε (x - y - shift) (x' - y' - shift)
    have hn : ‖x - y - shift - (x' - y' - shift)‖ ≤ ‖x - x'‖ + ‖y - y'‖ := by
      rw [show x - y - shift - (x' - y' - shift) = (x - x') - (y - y') by abel]
      exact norm_sub_le _ _
    exact h.trans (mul_le_mul_of_nonneg_left hn (sq_nonneg _))
  have he : cappedPairIntegrand ε shift (localizedRawDensity freq) (localizedRawDensity freq) (x, y) -
      cappedPairIntegrand ε shift (localizedRawDensity freq) (localizedRawDensity freq) (x', y') =
      (a - b) * k + b * (k - k') := by
    dsimp only [cappedPairIntegrand, a, b, k, k']
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg hk0, abs_of_nonneg hb0]
  have h1 := mul_le_mul hab hk1 hk0 (by
    have hL : 0 ≤ L := (abs_nonneg _).trans hx
    positivity)
  have h2 := (mul_le_of_le_one_left (abs_nonneg (k - k')) hb1).trans hkk
  nlinarith

end ContinuumCoulomb

end

end OAI
