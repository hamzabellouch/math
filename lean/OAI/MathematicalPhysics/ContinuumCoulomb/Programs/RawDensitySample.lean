import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.GaussianPacketProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.CappedKernelProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedRawDensity
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.ComputableResolvent
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.NumericalSquare

namespace OAI

/-! Literal bounded samples of the actual unnormalized three-dimensional
localized density, including the irrational fixed transverse frequency. -/

noncomputable section
namespace ContinuumCoulomb.RawDensitySample
open ExactQuantumFactoring.BitStackProgram

abbrev Input := (ℕ × ℕ) × CappedKernelProgram.Triple

def planarArgument (x : Input) : ResolventSchedule.Input :=
  ((2 * x.1.1, x.1.2), (x.2.1, x.2.2.1))

def verticalArgument (x : Input) : GaussianPacket.Input := (x.1, x.2.2.2)

def value (rho : ℕ) (x : Input) : ℚ :=
  rationalUnitClamp (ResolventSchedule.approximate (planarArgument x)) ^ 2 *
    GaussianPacket.approximate rho (verticalArgument x)

theorem value_nonnegative (rho : ℕ) (x : Input) : 0 ≤ value rho x :=
  mul_nonneg (sq_nonneg _) (rationalUnitClamp_nonnegative _)

theorem value_le_one (rho : ℕ) (x : Input) : value rho x ≤ 1 := by
  have hs := (sq_le_sq₀ (rationalUnitClamp_nonnegative _) zero_le_one).mpr
    (rationalUnitClamp_le_one (ResolventSchedule.approximate (planarArgument x)))
  exact (mul_le_mul hs (rationalUnitClamp_le_one _)
    (rationalUnitClamp_nonnegative _) (by positivity)).trans_eq (by norm_num)

theorem position_split (q : CappedKernelProgram.Triple) :
    positionSplitCoordinates (CappedKernelProgram.position q) =
      (PlanarForcingProgram.position (q.1, q.2.1), (q.2.2 : ℝ)) := by
  apply Prod.ext
  · ext i
    fin_cases i <;> rfl
  · rfl

theorem planar_norm_le (x : Input)
    (hx : |(x.2.1 : ℝ)| ≤ (x.1.1 : ℝ)) (hy : |(x.2.2.1 : ℝ)| ≤ (x.1.1 : ℝ)) :
    ‖PlanarForcingProgram.position (x.2.1, x.2.2.1)‖ ≤ (2 * x.1.1 : ℕ) := by
  have hx2 := (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _)).mpr hx
  have hy2 := (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg _)).mpr hy
  rw [sq_abs] at hx2 hy2
  apply (sq_le_sq₀ (norm_nonneg _) (Nat.cast_nonneg _)).mp
  rw [PlanarForcingProgram.position_norm_sq]
  push_cast
  nlinarith [sq_nonneg (x.1.1 : ℝ)]

theorem unit_product_error {a b a' b' ε δ : ℝ}
    (ha'0 : 0 ≤ a') (ha'1 : a' ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (ha : |a' - a| ≤ ε) (hb : |b' - b| ≤ δ) :
    |a' * b' - a * b| ≤ ε + δ := by
  have he : a' * b' - a * b = a' * (b' - b) + (a' - a) * b := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg ha'0, abs_of_nonneg hb0]
  have h1 := mul_le_of_le_one_left (abs_nonneg (b' - b)) ha'1
  have h2 := mul_le_of_le_one_right (abs_nonneg (a' - a)) hb1
  linarith

theorem value_error (rho : ℕ) (x : Input)
    (hx : |(x.2.1 : ℝ)| ≤ (x.1.1 : ℝ)) (hy : |(x.2.2.1 : ℝ)| ≤ (x.1.1 : ℝ))
    (hz : |(x.2.2.2 : ℝ)| ≤ (x.1.1 : ℝ)) :
    |(value rho x : ℝ) -
      localizedRawDensity (GaussianFrequency.frequency rho) (CappedKernelProgram.position x.2)| ≤
      4 * ((x.1.2 : ℝ) + 1)⁻¹ := by
  let r := PlanarForcingProgram.position (x.2.1, x.2.2.1)
  let a : ℝ := rationalUnitClamp (ResolventSchedule.approximate (planarArgument x))
  let b : ℝ := GaussianPacket.approximate rho (verticalArgument x)
  have hφ := ResolventSchedule.approximation_error (planarArgument x) (planar_norm_le x hx hy)
  have ha : |a - planarResolventMode r| ≤ ((x.1.2 : ℝ) + 1)⁻¹ :=
    (rationalUnitClamp_error _ (planarResolventMode_positive r).le
      (planarResolventMode_le_one r)).trans hφ
  have hε : ((x.1.2 : ℝ) + 1)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity)).mpr (by linarith [show (0 : ℝ) ≤ x.1.2 from Nat.cast_nonneg _])
  have ha2 := unitInterval_square_error (planarResolventMode_positive r).le
    (planarResolventMode_le_one r) hε ha
  have hb := GaussianPacket.approximation_error rho (verticalArgument x) hz
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    exact_mod_cast rationalUnitClamp_nonnegative (ResolventSchedule.approximate (planarArgument x))
  have ha1 : a ≤ 1 := by
    dsimp only [a]
    exact_mod_cast rationalUnitClamp_le_one (ResolventSchedule.approximate (planarArgument x))
  have hsq : a ^ 2 ≤ 1 := by simpa only [one_pow] using (sq_le_sq₀ ha0 zero_le_one).mpr ha1
  have hexp : Real.exp (-GaussianFrequency.frequency rho * (x.2.2.2 : ℝ) ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Real.sqrt_nonneg _)) (sq_nonneg _))
  have hp := unit_product_error (sq_nonneg a) hsq (Real.exp_pos _).le hexp ha2 hb
  have hout : |(value rho x : ℝ) -
      localizedRawDensity (GaussianFrequency.frequency rho) (CappedKernelProgram.position x.2)| ≤
      3 * ((x.1.2 : ℝ) + 1)⁻¹ + ((x.1.2 : ℝ) + 1)⁻¹ := by
    simpa only [value, Rat.cast_mul, Rat.cast_pow, localizedRawDensity, position_split,
      Prod.fst, Prod.snd, r, a, b, verticalArgument] using hp
  convert hout using 1
  ring

end ContinuumCoulomb.RawDensitySample

end

end OAI
