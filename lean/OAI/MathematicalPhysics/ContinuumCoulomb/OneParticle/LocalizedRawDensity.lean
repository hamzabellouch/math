import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedCoulombBox

namespace OAI

/-! Unnormalized packets used by the literal Coulomb quadrature. Squaring
the normalization cancels the Gaussian square root, so the final quotient
uses only the already certified planar mass, frequency and pi evaluators. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def localizedRawDensity (freq : ℝ) (x : Position) : ℝ :=
  planarResolventMode (positionSplitCoordinates x).1 ^ 2 *
    Real.exp (-freq * (positionSplitCoordinates x).2 ^ 2)

def localizedRawMass (freq : ℝ) : ℝ :=
  (∫ r, planarResolventMode r ^ 2) * Real.sqrt (Real.pi / freq)

theorem localizedRawMass_positive {freq : ℝ} (hfreq : 0 < freq) :
    0 < localizedRawMass freq :=
  mul_pos planarResolventMode_square_integral_positive
    (Real.sqrt_pos.mpr (div_pos Real.pi_pos hfreq))

theorem localizedRawDensity_nonnegative (freq : ℝ) (x : Position) :
    0 ≤ localizedRawDensity freq x :=
  mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

theorem localizedRawDensity_le_one {freq : ℝ} (hfreq : 0 ≤ freq) (x : Position) :
    localizedRawDensity freq x ≤ 1 := by
  have hp := (sq_le_sq₀ (planarResolventMode_positive _).le zero_le_one).mpr
    (planarResolventMode_le_one (positionSplitCoordinates x).1)
  have he : Real.exp (-freq * (positionSplitCoordinates x).2 ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hfreq) (sq_nonneg _))
  exact (mul_le_mul hp he (Real.exp_pos _).le (by positivity)).trans_eq (by norm_num)

theorem localizedRawDensity_eq_normalized {freq : ℝ} (hfreq : 0 < freq) (x : Position) :
    localizedRawDensity freq x = localizedRawMass freq * localizedDensity freq 0 x := by
  have hA := planarResolventMode_square_integral_positive
  have hB := Real.sqrt_pos.mpr (div_pos Real.pi_pos hfreq)
  simp only [localizedRawDensity, localizedRawMass, localizedDensity,
    continuumLocalizedMode, localizedMode, sub_zero, mul_pow, normalizedPlanarMode,
    div_pow, verticalMode_square hfreq, Real.sq_sqrt hA.le]
  field_simp

theorem localizedRawDensity_integrable {freq : ℝ} (hfreq : 0 < freq) :
    Integrable (localizedRawDensity freq) := by
  change Integrable (fun x => localizedRawDensity freq x)
  simp_rw [localizedRawDensity_eq_normalized hfreq]
  exact (localizedDensity_integrable hfreq 0).const_mul _

theorem localizedRawDensity_mass {freq : ℝ} (hfreq : 0 < freq) :
    (∫ x, localizedRawDensity freq x) = localizedRawMass freq := by
  simp_rw [localizedRawDensity_eq_normalized hfreq]
  rw [integral_const_mul, localizedDensity_mass hfreq 0, mul_one]

theorem localizedRawMass_square {freq : ℝ} (hfreq : 0 < freq) :
    localizedRawMass freq ^ 2 = (∫ r, planarResolventMode r ^ 2) ^ 2 * Real.pi / freq := by
  rw [localizedRawMass, mul_pow, Real.sq_sqrt (div_pos Real.pi_pos hfreq).le]
  ring

def localizedRawCoulombBox (freq ε L : ℝ) (u : PlanarPosition) : ℝ :=
  ∫ p in coulombNumericalBox L ×ˢ coulombNumericalBox L,
    cappedPairIntegrand ε (planarCenter u) (localizedRawDensity freq) (localizedRawDensity freq) p

theorem localizedRawCoulombBox_eq {freq : ℝ} (hfreq : 0 < freq) (ε L : ℝ)
    (u : PlanarPosition) :
    localizedRawCoulombBox freq ε L u =
      localizedRawMass freq ^ 2 * localizedCoulombBoxIntegral freq ε L u := by
  unfold localizedRawCoulombBox localizedCoulombBoxIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with p
  simp only [cappedPairIntegrand, localizedRawDensity_eq_normalized hfreq]
  ring

theorem localizedRawCoulombBox_quotient {freq : ℝ} (hfreq : 0 < freq) (ε L : ℝ)
    (u : PlanarPosition) :
    localizedRawCoulombBox freq ε L u * freq /
      ((∫ r, planarResolventMode r ^ 2) ^ 2 * Real.pi) =
        localizedCoulombBoxIntegral freq ε L u := by
  rw [localizedRawCoulombBox_eq hfreq, localizedRawMass_square hfreq]
  have hA := planarResolventMode_square_integral_positive.ne'
  have hpi := Real.pi_pos.ne'
  field_simp

end ContinuumCoulomb

end

end OAI
