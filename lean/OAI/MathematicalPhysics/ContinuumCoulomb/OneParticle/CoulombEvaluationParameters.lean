import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombQuadratureBudget
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombTruncationSchedule
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.RawCoulombMassBound

namespace OAI

/-! One fixed set of polynomial precision parameters for the actual
localized Coulomb coefficient. Only the requested accuracy varies. -/

noncomputable section
namespace ContinuumCoulomb.CoulombEvaluation

def frequencyBound (rho : ℕ) : ℕ := ⌈GaussianFrequency.frequency rho⌉₊ + 1
def normalizationBound (rho : ℕ) : ℕ :=
  ⌈max 1 (CoulombNormalization.coefficient (GaussianFrequency.frequency rho))⌉₊ + 1
def rawMassBound (rho : ℕ) : ℕ :=
  ⌈localizedRawMass (GaussianFrequency.frequency rho) ^ 2 + 1⌉₊ + 1

def truncationPrecision (P : ℕ) : ℕ := 4 * (P + 1)
def denominator (rho P : ℕ) : ℕ :=
  CoulombTruncationSchedule.guard (GaussianFrequency.frequency rho) *
    CoulombTruncationSchedule.scale (truncationPrecision P)
def radius (rho P : ℕ) : ℕ :=
  CoulombTruncationSchedule.radius (GaussianFrequency.frequency rho) (truncationPrecision P)
def rawPrecision (rho P : ℕ) : ℕ := 4 * normalizationBound rho * (P + 1)
def mesh (rho P : ℕ) : ℕ := CoulombQuadratureSchedule.mesh
  (frequencyBound rho) (radius rho P) (denominator rho P) (rawPrecision rho P)
def samplePrecision (rho P : ℕ) : ℕ := CoulombQuadratureSchedule.accuracy
  (radius rho P) (denominator rho P) (rawPrecision rho P)
def kernelPrecision (rho P : ℕ) : ℕ := CoulombQuadratureSchedule.kernelPrecision
  (radius rho P) (denominator rho P) (rawPrecision rho P)
def normalizationPrecision (rho P : ℕ) : ℕ := 8 * rawMassBound rho * denominator rho P * (P + 1)

def input (rho P : ℕ) (d : ℚ) : RationalSixQuadrature.Input RawCoulombSample.Settings :=
  RawCoulombSample.quadratureInput (radius rho P) (samplePrecision rho P) (kernelPrecision rho P)
    (1 / (denominator rho P : ℚ)) (d, 0, 0) (mesh rho P)

def rawApproximate (rho P : ℕ) (d : ℚ) : ℚ :=
  RationalSixQuadrature.value (RawCoulombSample.sixEvaluator rho) (input rho P d)

def approximate (rho P : ℕ) (d : ℚ) : ℚ :=
  CoulombNormalization.approximate rho (normalizationPrecision rho P) * rawApproximate rho P d

theorem frequencyBound_le (rho : ℕ) : GaussianFrequency.frequency rho ≤ (frequencyBound rho : ℝ) := by
  have h := Nat.le_ceil (GaussianFrequency.frequency rho)
  simp only [frequencyBound, Nat.cast_add, Nat.cast_one]
  linarith

theorem normalizationBound_bounds (rho : ℕ) :
    1 ≤ (normalizationBound rho : ℝ) ∧
      CoulombNormalization.coefficient (GaussianFrequency.frequency rho) ≤ normalizationBound rho := by
  have h := Nat.le_ceil (max 1 (CoulombNormalization.coefficient (GaussianFrequency.frequency rho)))
  have h1 := (le_max_left (1 : ℝ) _).trans h
  have h2 := (le_max_right (1 : ℝ) _).trans h
  simp only [normalizationBound, Nat.cast_add, Nat.cast_one]
  constructor <;> linarith

theorem rawMassBound_le (rho : ℕ) :
    localizedRawMass (GaussianFrequency.frequency rho) ^ 2 + 1 ≤ (rawMassBound rho : ℝ) := by
  have h := Nat.le_ceil (localizedRawMass (GaussianFrequency.frequency rho) ^ 2 + 1)
  simp only [rawMassBound, Nat.cast_add, Nat.cast_one]
  linarith

theorem denominator_positive (rho P : ℕ) : 0 < denominator rho P := by
  have hg := CoulombTruncationSchedule.guard_one_le (GaussianFrequency.frequency rho)
  have hs := CoulombTruncationSchedule.scale_eight_le (truncationPrecision P)
  have h : (0 : ℝ) < denominator rho P := by
    simp only [denominator, Nat.cast_mul]
    positivity
  exact_mod_cast h

theorem radius_positive (rho P : ℕ) : 0 < radius rho P := by
  exact_mod_cast CoulombTruncationSchedule.radius_positive
    (GaussianFrequency.frequency rho) (truncationPrecision P)

theorem rawPrecision_positive (rho P : ℕ) : 0 < rawPrecision rho P := by
  have hc : 0 < normalizationBound rho := by
    have h := (normalizationBound_bounds rho).1
    exact_mod_cast (show (0 : ℝ) < normalizationBound rho by linarith)
  unfold rawPrecision
  positivity

theorem mesh_positive (rho P : ℕ) : 0 < mesh rho P := by
  have hR := radius_positive rho P
  have hD := denominator_positive rho P
  have hS := rawPrecision_positive rho P
  have hA : 0 < 64 + 2 * frequencyBound rho * radius rho P := by omega
  have hL : 0 < CoulombQuadratureSchedule.lipschitz (frequencyBound rho)
      (radius rho P) (denominator rho P) := by
    unfold CoulombQuadratureSchedule.lipschitz
    exact lt_of_lt_of_le (Nat.mul_pos hA hD) (Nat.le_add_right _ _)
  have hV : 0 < CoulombQuadratureSchedule.volume (radius rho P) := by
    change 0 < (2 * radius rho P) ^ 6
    exact pow_pos (Nat.mul_pos (by decide) hR) _
  change 0 < 48 * radius rho P *
    CoulombQuadratureSchedule.lipschitz (frequencyBound rho) (radius rho P) (denominator rho P) *
      CoulombQuadratureSchedule.volume (radius rho P) * rawPrecision rho P
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) hR) hL) hV) hS

theorem epsilon_eq (rho P : ℕ) :
    (1 / (denominator rho P : ℚ) : ℝ) =
      (CoulombTruncationSchedule.epsilon (GaussianFrequency.frequency rho) (truncationPrecision P) : ℝ) := by
  simp only [denominator, CoulombTruncationSchedule.epsilon, Rat.cast_div, Rat.cast_one,
    Rat.cast_natCast, Rat.cast_mul, Nat.cast_mul]

end ContinuumCoulomb.CoulombEvaluation

end

end OAI
