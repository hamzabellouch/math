import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourcePositiveCorrectness

namespace OAI

/-! The literal positive-spin thresholds retain a quantitative part of the
rounding budget. This margin pays for the later Hubbard and continuum errors. -/

noncomputable section
namespace ContinuumCoulomb.SourceNormalizedSpectrum

theorem normalization_margin (r : ℕ) {G : ℕ} (hG : 0 < G) :
    3 / (512 * (G : ℝ)) + 3 * r / (2 * (denominator r G : ℝ)) +
      1 / (2048 * (G : ℝ)) ≤ 1 / (128 * (G : ℝ)) := by
  have hg : (0 : ℝ) < G := by exact_mod_cast hG
  have hden : (denominator r G : ℝ) = 1024 * ((r : ℝ) + 1) * G := by
    simp only [denominator,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  rw [hden]
  have hr : 3 * (r : ℝ) / (2 * (1024 * (r + 1) * G)) ≤ 3 / (2048 * G) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have he : 3 / (512 * (G : ℝ)) + 3 / (2048 * G) + 1 / (2048 * G) =
      1 / (128 * G) := by field_simp; ring
  linarith

theorem source_positive_margin (d : SquareLatticeHeisenberg) {W G : ℕ}
    (hG : 0 < G) (hW : ∀ e, |(d.coefficient e : ℝ)| ≤ W) :
    |positiveEnergy d W G +
      (MediatorIteration.offset (family d (denominator d.edges G))
        (denominator d.edges G + W + 1) G : ℝ) - realSourceGroundEnergy d| +
      1 / (2048 * (G : ℝ)) ≤ 1 / (128 * (G : ℝ)) := by
  have h := normalized_three_stage_bottom d (denominator_pos d.edges hG) hG hW
  exact (add_le_add h le_rfl).trans (normalization_margin d.edges hG)

theorem source_positive_yes_margin (d : SquareLatticeHeisenberg) {W G : ℕ}
    (hG : 0 < G) (hW : ∀ e, |(d.coefficient e : ℝ)| ≤ W) {a : ℚ}
    (hyes : realSourceGroundEnergy d ≤ a) :
    positiveEnergy d W G + 1 / (2048 * (G : ℝ)) ≤ lowerThreshold d W G a := by
  have hm := source_positive_margin d hG hW
  have ha := le_abs_self (positiveEnergy d W G +
    (MediatorIteration.offset (family d (denominator d.edges G))
      (denominator d.edges G + W + 1) G : ℝ) - realSourceGroundEnergy d)
  simp only [lowerThreshold,Rat.cast_add,Rat.cast_sub,Rat.cast_div,
    Rat.cast_mul,Rat.cast_one,Rat.cast_ofNat,Rat.cast_natCast]
  linarith

theorem source_positive_no_margin (d : SquareLatticeHeisenberg) {W G : ℕ}
    (hG : 0 < G) (hW : ∀ e, |(d.coefficient e : ℝ)| ≤ W) {b : ℚ}
    (hno : (b : ℝ) ≤ realSourceGroundEnergy d) :
    (upperThreshold d W G b : ℝ) + 1 / (2048 * (G : ℝ)) ≤ positiveEnergy d W G := by
  have hm := source_positive_margin d hG hW
  have ha := neg_abs_le (positiveEnergy d W G +
    (MediatorIteration.offset (family d (denominator d.edges G))
      (denominator d.edges G + W + 1) G : ℝ) - realSourceGroundEnergy d)
  simp only [upperThreshold,Rat.cast_sub,Rat.cast_div,
    Rat.cast_mul,Rat.cast_one,Rat.cast_ofNat,Rat.cast_natCast]
  linarith

end ContinuumCoulomb.SourceNormalizedSpectrum

namespace ContinuumCoulomb.SourcePositiveProgram
open SourceMetadataProgram

theorem output_yes_margin (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid)
    (hp : d.PolynomialPromise k)
    (hyes : realSourceGroundEnergy (d.toSource h) ≤ d.lower.value) :
    energy (output k d) + 1 / (2048 * ((size d ^ k : ℕ) : ℝ)) ≤
      (output k d).lower := by
  rw [energy_eq k d h,lower_eq k d h]
  exact SourceNormalizedSpectrum.source_positive_yes_margin _ (pow_pos (size_pos d) k)
    (polynomialPromise_weight k d h hp) hyes

theorem output_no_margin (k : ℕ) (d : BinaryHeisenberg) (h : d.Valid)
    (hp : d.PolynomialPromise k)
    (hno : (d.upper.value : ℝ) ≤ realSourceGroundEnergy (d.toSource h)) :
    ((output k d).upper : ℝ) + 1 / (2048 * ((size d ^ k : ℕ) : ℝ)) ≤
      energy (output k d) := by
  rw [energy_eq k d h,upper_eq k d h]
  exact SourceNormalizedSpectrum.source_positive_no_margin _ (pow_pos (size_pos d) k)
    (polynomialPromise_weight k d h hp) hno

end ContinuumCoulomb.SourcePositiveProgram

end

end OAI
