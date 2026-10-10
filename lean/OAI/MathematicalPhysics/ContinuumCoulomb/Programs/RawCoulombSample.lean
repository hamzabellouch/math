import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.RawDensitySampleProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CappedRawModulus

namespace OAI

/-! A literal rational sample of the six-coordinate Coulomb integrand.
Both density factors and the capped kernel use the certified programs. -/

noncomputable section
namespace ContinuumCoulomb.RawCoulombSample
open CappedKernelProgram

def difference (x y s : Triple) : Triple :=
  (x.1 - y.1 - s.1, x.2.1 - y.2.1 - s.2.1, x.2.2 - y.2.2 - s.2.2)

theorem position_difference (x y s : Triple) :
    position (difference x y s) = position x - position y - position s := by
  ext i
  fin_cases i <;> simp [position, difference]

def value (rho R P b : ℕ) (ε : ℚ) (s x y : Triple) : ℚ :=
  RawDensitySample.value rho ((R, P), x) * RawDensitySample.value rho ((R, P), y) *
    approximate ((b, ε), difference x y s)

def inBox (R : ℕ) (x : Triple) : Prop :=
  |(x.1 : ℝ)| ≤ R ∧ |(x.2.1 : ℝ)| ≤ R ∧ |(x.2.2 : ℝ)| ≤ R

theorem kernel_nonnegative (b : ℕ) {ε : ℚ} (hε : 0 < ε) (q : Triple) :
    (0 : ℝ) ≤ approximate ((b, ε), q) := by
  simp only [approximate, Rat.cast_inv, Rat.cast_max]
  exact inv_nonneg.mpr ((show (0 : ℝ) ≤ ε by exact_mod_cast hε.le).trans (le_max_left _ _))

theorem kernel_le (b : ℕ) {ε : ℚ} (hε : 0 < ε) (q : Triple) :
    (approximate ((b, ε), q) : ℝ) ≤ (ε : ℝ)⁻¹ := by
  simp only [approximate, Rat.cast_inv, Rat.cast_max]
  exact inv_anti₀ (by exact_mod_cast hε) (le_max_left _ _)

theorem value_error (rho R P b : ℕ) {ε : ℚ} (hε : 0 < ε)
    (s x y : Triple) (hx : inBox R x) (hy : inBox R y) :
    |(value rho R P b ε s x y : ℝ) -
      cappedPairIntegrand (ε : ℝ) (position s)
        (localizedRawDensity (GaussianFrequency.frequency rho))
        (localizedRawDensity (GaussianFrequency.frequency rho)) (position x, position y)| ≤
      8 * (ε : ℝ)⁻¹ * ((P : ℝ) + 1)⁻¹ + (ε : ℝ)⁻¹ ^ 2 * (2 : ℝ)⁻¹ ^ b := by
  let f := localizedRawDensity (GaussianFrequency.frequency rho)
  let a : ℝ := RawDensitySample.value rho ((R, P), x)
  let c : ℝ := RawDensitySample.value rho ((R, P), y)
  let k : ℝ := approximate ((b, ε), difference x y s)
  let t := cappedCoulombKernel (ε : ℝ) (position x - position y - position s)
  have hfreq : 0 ≤ GaussianFrequency.frequency rho := Real.sqrt_nonneg _
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    exact_mod_cast RawDensitySample.value_nonnegative rho ((R, P), x)
  have ha1 : a ≤ 1 := by
    dsimp only [a]
    exact_mod_cast RawDensitySample.value_le_one rho ((R, P), x)
  have hprod := bounded_product_sub (a := a) (b := c) (c := f (position x))
    (d := f (position y)) ha0 ha1
    (localizedRawDensity_nonnegative _ _) (localizedRawDensity_le_one hfreq _)
  have hxerr := RawDensitySample.value_error rho ((R, P), x) hx.1 hx.2.1 hx.2.2
  have hyerr := RawDensitySample.value_error rho ((R, P), y) hy.1 hy.2.1 hy.2.2
  have herr : |a * c - f (position x) * f (position y)| ≤ 8 * ((P : ℝ) + 1)⁻¹ := by
    exact hprod.trans (by dsimp only [a, c, f] at *; linarith)
  have hk0 : 0 ≤ k := kernel_nonnegative b hε _
  have hk1 : k ≤ (ε : ℝ)⁻¹ := kernel_le b hε _
  have hkerr : |k - t| ≤ (ε : ℝ)⁻¹ ^ 2 * (2 : ℝ)⁻¹ ^ b := by
    have h := approximation_error ((b, ε), difference x y s) hε
    simpa only [position_difference] using h
  have hf0 : 0 ≤ f (position x) * f (position y) :=
    mul_nonneg (localizedRawDensity_nonnegative _ _) (localizedRawDensity_nonnegative _ _)
  have hf1 : f (position x) * f (position y) ≤ 1 := by
    exact (mul_le_mul (localizedRawDensity_le_one hfreq _) (localizedRawDensity_le_one hfreq _)
      (localizedRawDensity_nonnegative _ _) zero_le_one).trans_eq (one_mul 1)
  have he : (value rho R P b ε s x y : ℝ) -
      cappedPairIntegrand (ε : ℝ) (position s) f f (position x, position y) =
      (a * c - f (position x) * f (position y)) * k +
        f (position x) * f (position y) * (k - t) := by
    simp only [value, Rat.cast_mul, cappedPairIntegrand, a, c, k, t]
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg hk0, abs_of_nonneg hf0]
  have h1 := mul_le_mul herr hk1 hk0 (by positivity)
  have h2 := (mul_le_of_le_one_left (abs_nonneg (k - t)) hf1).trans hkerr
  nlinarith

end ContinuumCoulomb.RawCoulombSample

end

end OAI
