import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceNormalizedSpectrum

namespace OAI

/-! A fixed polynomial common denominator absorbs both coefficient rounding
and all three mediator errors into one inverse-polynomial promise budget. -/

noncomputable section
namespace ContinuumCoulomb.SourceNormalizedSpectrum

def denominator (r G : ℕ) : ℕ := 1024 * (r + 1) * G

theorem denominator_pos (r : ℕ) {G : ℕ} (hG : 0 < G) : 0 < denominator r G := by
  unfold denominator
  positivity

theorem normalization_budget (r : ℕ) {G : ℕ} (hG : 0 < G) :
    3 / (512 * (G : ℝ)) + 3 * r / (2 * (denominator r G : ℝ)) ≤
      1 / (128 * (G : ℝ)) := by
  have hg : (0 : ℝ) < G := by exact_mod_cast hG
  have hden : (denominator r G : ℝ) = 1024 * ((r : ℝ) + 1) * G := by
    simp only [denominator, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  rw [hden]
  have hround : 3 * (r : ℝ) / (2 * (1024 * (r + 1) * G)) ≤ 3 / (2048 * G) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  calc
    _ ≤ 3 / (512 * (G : ℝ)) + 3 / (2048 * G) := add_le_add le_rfl hround
    _ ≤ _ := by
      field_simp
      nlinarith

/-- The original source permits arbitrarily small and zero rational
coefficients. This complete positive-spin comparison does too. -/
theorem source_positive_bottom (d : SquareLatticeHeisenberg) {W G : ℕ}
    (hG : 0 < G) (hW : ∀ e, |(d.coefficient e : ℝ)| ≤ W) :
    |sourceMatrixBottom
      (d.vertices + (retained d (denominator d.edges G)).length * 2 +
        (retained d (denominator d.edges G)).length * 2 * 2 +
        ((retained d (denominator d.edges G)).length * 2 +
          (retained d (denominator d.edges G)).length * 2 * 2) * 2)
      (MediatorIteration.finalGraph (family d (denominator d.edges G))
        (denominator d.edges G + W + 1) G).matrix +
      (MediatorIteration.offset (family d (denominator d.edges G))
        (denominator d.edges G + W + 1) G : ℝ) - realSourceGroundEnergy d| ≤
      1 / (128 * (G : ℝ)) :=
  (normalized_three_stage_bottom d (denominator_pos d.edges hG) hG hW).trans
    (normalization_budget d.edges hG)

def lowerThreshold (d : SquareLatticeHeisenberg) (W G : ℕ) (a : ℚ) : ℚ :=
  a - MediatorIteration.offset (family d (denominator d.edges G))
    (denominator d.edges G + W + 1) G + 1 / (128 * (G : ℚ))

def upperThreshold (d : SquareLatticeHeisenberg) (W G : ℕ) (b : ℚ) : ℚ :=
  b - MediatorIteration.offset (family d (denominator d.edges G))
    (denominator d.edges G + W + 1) G - 1 / (128 * (G : ℚ))

def positiveEnergy (d : SquareLatticeHeisenberg) (W G : ℕ) : ℝ :=
  sourceMatrixBottom _
    (MediatorIteration.finalGraph (family d (denominator d.edges G))
      (denominator d.edges G + W + 1) G).matrix

theorem source_positive_yes (d : SquareLatticeHeisenberg) {W G : ℕ}
    (hG : 0 < G) (hW : ∀ e, |(d.coefficient e : ℝ)| ≤ W) {a : ℚ}
    (hyes : realSourceGroundEnergy d ≤ a) :
    positiveEnergy d W G ≤ lowerThreshold d W G a := by
  have he := (abs_le.mp (source_positive_bottom d hG hW)).2
  change positiveEnergy d W G + _ - realSourceGroundEnergy d ≤ _ at he
  simp only [lowerThreshold, Rat.cast_add, Rat.cast_sub, Rat.cast_div,
    Rat.cast_mul, Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast]
  linarith

theorem source_positive_no (d : SquareLatticeHeisenberg) {W G : ℕ}
    (hG : 0 < G) (hW : ∀ e, |(d.coefficient e : ℝ)| ≤ W) {b : ℚ}
    (hno : (b : ℝ) ≤ realSourceGroundEnergy d) :
    (upperThreshold d W G b : ℝ) ≤ positiveEnergy d W G := by
  have he := (abs_le.mp (source_positive_bottom d hG hW)).1
  change _ ≤ positiveEnergy d W G + _ - realSourceGroundEnergy d at he
  simp only [upperThreshold, Rat.cast_sub, Rat.cast_div, Rat.cast_mul,
    Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast]
  linarith

theorem positive_threshold_gap (d : SquareLatticeHeisenberg) (W G : ℕ) {a b : ℚ}
    (hgap : 1 / (G : ℚ) ≤ b - a) :
    63 / 64 * (b - a) ≤ upperThreshold d W G b - lowerThreshold d W G a := by
  have heq : 1 / (128 * (G : ℚ)) + 1 / (128 * (G : ℚ)) =
      1 / 64 * (1 / (G : ℚ)) := by ring
  unfold upperThreshold lowerThreshold
  linarith

end ContinuumCoulomb.SourceNormalizedSpectrum

end

end OAI
