import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.GaussianFrequencyProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalClamp
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.RationalExponentialProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.HeatKernelModulus

namespace OAI

/-! A certified rational sample of the actual transverse Gaussian. The
frequency is sqrt(4*pi*rho), with rho fixed, and is evaluated internally. -/

noncomputable section
namespace ContinuumCoulomb.GaussianPacket

abbrev Input := (ℕ × ℕ) × ℚ

def frequencyPrecision (R P : ℕ) : ℕ := 16 * (R + 1) ^ 2 * (P + 1)
def exponentialPrecision (P : ℕ) : ℕ := 8 * (P + 1)
def magnitude (rho R : ℕ) : ℕ := (4 * rho + 4) * (R + 1) ^ 2

def exponent (rho : ℕ) (x : Input) : ℚ :=
  -GaussianFrequency.approximate rho (frequencyPrecision x.1.1 x.1.2) * x.2 ^ 2

def argument (rho : ℕ) (x : Input) : RationalExponentialProgram.Input :=
  (magnitude rho x.1.1, (exponentialPrecision x.1.2, exponent rho x))

def approximate (rho : ℕ) (x : Input) : ℚ :=
  rationalUnitClamp (RationalExponentialProgram.approximate (argument rho x))

theorem frequencyApprox_nonnegative (rho P : ℕ) :
    0 ≤ GaussianFrequency.approximate rho P := by
  unfold GaussianFrequency.approximate RationalSquareRoot.value DyadicRootProgram.value
  positivity

theorem frequency_le (rho : ℕ) : GaussianFrequency.frequency rho ≤ 4 * (rho : ℝ) + 2 := by
  unfold GaussianFrequency.frequency
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hpi := Real.pi_lt_four
    nlinarith [sq_nonneg (rho : ℝ), show (0 : ℝ) ≤ rho from Nat.cast_nonneg _]

theorem frequencyApprox_le (rho P : ℕ) :
    (GaussianFrequency.approximate rho P : ℝ) ≤ 4 * (rho : ℝ) + 3 := by
  have h := (abs_le.mp (GaussianFrequency.approximation_error rho P)).2
  have hp : ((P : ℝ) + 1)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity)).mpr (by linarith [show (0 : ℝ) ≤ P from Nat.cast_nonneg _])
  linarith [frequency_le rho]

theorem exponent_nonpositive (rho : ℕ) (x : Input) : (exponent rho x : ℝ) ≤ 0 := by
  simp only [exponent, Rat.cast_mul, Rat.cast_neg, Rat.cast_pow]
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (by exact_mod_cast frequencyApprox_nonnegative rho _)) (sq_nonneg _)

theorem exponent_abs_le (rho : ℕ) (x : Input) (hz : |(x.2 : ℝ)| ≤ x.1.1) :
    |(exponent rho x : ℝ)| ≤ (magnitude rho x.1.1 : ℝ) := by
  rw [abs_of_nonpos (exponent_nonpositive rho x)]
  simp only [exponent, Rat.cast_mul, Rat.cast_neg, Rat.cast_pow, neg_mul, neg_neg]
  have hz'' : (x.2 : ℝ) ^ 2 ≤ ((x.1.1 : ℝ) + 1) ^ 2 := by
    have habs := (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _)).mpr hz
    rw [sq_abs] at habs
    nlinarith [show (0 : ℝ) ≤ x.1.1 from Nat.cast_nonneg _]
  calc
    _ ≤ (4 * (rho : ℝ) + 3) * (((x.1.1 : ℝ) + 1) ^ 2) :=
      mul_le_mul (frequencyApprox_le rho _) hz'' (sq_nonneg _)
        (by positivity)
    _ ≤ _ := by
      simp only [magnitude, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_one]
      nlinarith [sq_nonneg ((x.1.1 : ℝ) + 1)]

theorem exponent_error (rho : ℕ) (x : Input) (hz : |(x.2 : ℝ)| ≤ x.1.1) :
    |(exponent rho x : ℝ) - (-GaussianFrequency.frequency rho * (x.2 : ℝ) ^ 2)| ≤
      (8 * ((x.1.2 : ℝ) + 1))⁻¹ := by
  have hfreq := GaussianFrequency.approximation_error rho (frequencyPrecision x.1.1 x.1.2)
  have hzsq : (x.2 : ℝ) ^ 2 ≤ ((x.1.1 : ℝ) + 1) ^ 2 := by
    have habs := (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _)).mpr hz
    rw [sq_abs] at habs
    nlinarith [show (0 : ℝ) ≤ x.1.1 from Nat.cast_nonneg _]
  have he : (exponent rho x : ℝ) - (-GaussianFrequency.frequency rho * (x.2 : ℝ) ^ 2) =
      -(GaussianFrequency.approximate rho (frequencyPrecision x.1.1 x.1.2) -
        GaussianFrequency.frequency rho) * (x.2 : ℝ) ^ 2 := by
    simp only [exponent, Rat.cast_mul, Rat.cast_neg, Rat.cast_pow]
    ring
  rw [he, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (x.2 : ℝ))]
  apply (mul_le_mul hfreq hzsq (sq_nonneg _) (by positivity)).trans
  have hR : 0 < ((x.1.1 : ℝ) + 1) ^ 2 := by positivity
  have hP : 0 < (x.1.2 : ℝ) + 1 := by positivity
  have hprec : (frequencyPrecision x.1.1 x.1.2 : ℝ) =
      16 * ((x.1.1 : ℝ) + 1) ^ 2 * ((x.1.2 : ℝ) + 1) := by
    simp only [frequencyPrecision, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
      Nat.cast_one, Nat.cast_pow]
  rw [hprec]
  calc
    _ ≤ (16 * ((x.1.1 : ℝ) + 1) ^ 2 * ((x.1.2 : ℝ) + 1))⁻¹ *
        ((x.1.1 : ℝ) + 1) ^ 2 := by gcongr; linarith
    _ = (16 * ((x.1.2 : ℝ) + 1))⁻¹ := by
      field_simp [hR.ne', hP.ne']
    _ ≤ _ := inv_anti₀ (by positivity) (by nlinarith)

theorem exponential_precision_bound (P : ℕ) :
    (2 : ℝ)⁻¹ ^ exponentialPrecision P ≤ (8 * ((P : ℝ) + 1))⁻¹ := by
  have hn := ResolventSchedule.succ_le_two_pow (exponentialPrecision P)
  have hp : 8 * (P + 1) ≤ 2 ^ exponentialPrecision P := by unfold exponentialPrecision at *; omega
  have hr : 8 * ((P : ℝ) + 1) ≤ (2 : ℝ) ^ exponentialPrecision P := by exact_mod_cast hp
  rw [inv_pow]
  exact inv_anti₀ (by positivity) hr

theorem approximation_error (rho : ℕ) (x : Input) (hz : |(x.2 : ℝ)| ≤ x.1.1) :
    |(approximate rho x : ℝ) - Real.exp (-GaussianFrequency.frequency rho * (x.2 : ℝ) ^ 2)| ≤
      ((x.1.2 : ℝ) + 1)⁻¹ := by
  have ht := RationalExponentialProgram.error (argument rho x) (exponent_abs_le rho x hz)
  rw [abs_sub_comm] at ht
  have hprec := exponential_precision_bound x.1.2
  rw [inv_pow] at hprec
  have htaylor := ht.trans hprec
  have harg : -GaussianFrequency.frequency rho * (x.2 : ℝ) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.sqrt_nonneg _)) (sq_nonneg _)
  have hexp := HeatKernelModulus.exp_nonpositive_lipschitz (exponent_nonpositive rho x) harg
  have hbase := (abs_sub_le (RationalExponentialProgram.approximate (argument rho x) : ℝ)
    (Real.exp (exponent rho x : ℝ))
    (Real.exp (-GaussianFrequency.frequency rho * (x.2 : ℝ) ^ 2))).trans
      (add_le_add htaylor
        (hexp.trans (exponent_error rho x hz)))
  apply (rationalUnitClamp_error _ (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr harg)).trans
  apply hbase.trans
  rw [mul_inv]
  norm_num
  nlinarith [inv_pos.mpr (show 0 < (x.1.2 : ℝ) + 1 by positivity)]

end ContinuumCoulomb.GaussianPacket

end

end OAI
