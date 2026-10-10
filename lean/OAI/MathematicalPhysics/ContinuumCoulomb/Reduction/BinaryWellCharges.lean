import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.BinaryAmplification
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.IsolatedPerturbation

namespace OAI

/-!
# The actual rounded binary-well charges

The integer charges are fixed before the secondary displacement is tuned.
Their normalized values satisfy explicit uniform smallness bounds, and their
binary lengths remain linear in the geometric scale. This is analytic and
encoding-size correctness. The charges themselves are computed by rational
arithmetic. The isolated-energy tuning algorithm is separate.
-/

open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def binaryPrimaryCharge (D m : ℕ) : ℕ :=
  rationalRoundedScaledCharge (binaryAmplification D) (1 - 500 * m / (D : ℚ))

def binarySecondaryCharge (D m : ℕ) : ℕ :=
  rationalRoundedScaledCharge (binaryAmplification D) (1000 * m / (D : ℚ))

noncomputable section

theorem binaryPrimaryCharge_eq (D m : ℕ) : binaryPrimaryCharge D m =
    roundedScaledCharge (binaryAmplification D) (1 - 500 * m / (D : ℝ)) := by
  simp only [binaryPrimaryCharge, rationalRoundedScaledCharge_eq, Rat.cast_sub,
    Rat.cast_one, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast]

theorem binarySecondaryCharge_eq (D m : ℕ) : binarySecondaryCharge D m =
    roundedScaledCharge (binaryAmplification D) (1000 * m / (D : ℝ)) := by
  simp only [binarySecondaryCharge, rationalRoundedScaledCharge_eq,
    Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast]

def binaryPrimaryRatio (D m : ℕ) : ℝ :=
  (binaryPrimaryCharge D m : ℝ) / binaryAmplification D

def binarySecondaryRatio (D m : ℕ) : ℝ :=
  (binarySecondaryCharge D m : ℝ) / binaryAmplification D

theorem binaryWellCharges_spec {D m : ℕ} (hm : 0 < m) (hscale : 2002 * m ≤ D) :
    0 < binaryPrimaryCharge D m ∧ 0 < binarySecondaryCharge D m ∧
      0 ≤ binaryPrimaryRatio D m ∧ binaryPrimaryRatio D m ≤ 1 ∧
      |1 - binaryPrimaryRatio D m| ≤ 501 * m / (D : ℝ) ∧
      999 * m / (D : ℝ) ≤ binarySecondaryRatio D m ∧
      binarySecondaryRatio D m ≤ 1001 * m / (D : ℝ) ∧
      binarySecondaryRatio D m ≤ 1 := by
  let Z : ℝ := binaryAmplification D
  let r : ℝ := m / (D : ℝ)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hDlarge : (2002 : ℝ) * m ≤ D := by exact_mod_cast hscale
  have hD : (0 : ℝ) < D := by linarith
  have hZpos : 0 < Z := by
    change (0 : ℝ) < binaryAmplification D
    exact_mod_cast binaryAmplification_pos D
  have hZlarge : (D : ℝ) + 1 ≤ Z := by
    change (D : ℝ) + 1 ≤ (binaryAmplification D : ℝ)
    exact_mod_cast binaryAmplification_ge_scale D
  have hrpos : 0 ≤ r := by dsimp [r]; positivity
  have hrsmall : r ≤ 1 / 2002 := by
    dsimp [r]
    apply (div_le_iff₀ hD).mpr
    linarith
  have hZr : 1 ≤ Z * r := by
    have h := mul_le_mul_of_nonneg_right (show (D : ℝ) ≤ Z by linarith) hrpos
    have heq : (D : ℝ) * r = m := by dsimp [r]; field_simp
    rw [heq] at h
    linarith
  have hpbase : 1 / 2 ≤ 1 - 500 * r := by linarith
  have hp : 1 ≤ Z * (1 - 500 * r) := by
    have hZ2 : 2 ≤ Z := by linarith
    calc
      (1 : ℝ) = 2 * (1 / 2) := by norm_num
      _ ≤ Z * (1 - 500 * r) := mul_le_mul hZ2 hpbase (by norm_num) hZpos.le
  have hs : 1 ≤ Z * (1000 * r) := by nlinarith
  have hp' : 1 ≤ (binaryAmplification D : ℝ) * (1 - 500 * m / (D : ℝ)) := by
    simpa only [Z, r, mul_div_assoc] using hp
  have hs' : 1 ≤ (binaryAmplification D : ℝ) * (1000 * m / (D : ℝ)) := by
    simpa only [Z, r, mul_div_assoc] using hs
  have hchargep := roundedScaledCharge_pos hp'
  have hcharges := roundedScaledCharge_pos hs'
  rw [← binaryPrimaryCharge_eq] at hchargep
  rw [← binarySecondaryCharge_eq] at hcharges
  have herror : 1 / (2 * Z) ≤ r := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * Z)).mpr
    nlinarith
  have hep := (roundedScaledCharge_error (binaryAmplification_pos D) hp').trans herror
  have hes := (roundedScaledCharge_error (binaryAmplification_pos D) hs').trans herror
  rw [← binaryPrimaryCharge_eq] at hep
  rw [← binarySecondaryCharge_eq] at hes
  change |binaryPrimaryRatio D m - (1 - 500 * m / (D : ℝ))| ≤ r at hep
  change |binarySecondaryRatio D m - (1000 * m / (D : ℝ))| ≤ r at hes
  have hep' : |binaryPrimaryRatio D m - (1 - 500 * r)| ≤ r := by
    simpa only [r, mul_div_assoc] using hep
  have hes' : |binarySecondaryRatio D m - 1000 * r| ≤ r := by
    simpa only [r, mul_div_assoc] using hes
  obtain ⟨hpl, hpu⟩ := abs_le.mp hep'
  obtain ⟨hsl, hsu⟩ := abs_le.mp hes'
  refine ⟨hchargep, hcharges, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [binaryPrimaryRatio]
    positivity
  · linarith
  · rw [show (501 : ℝ) * m / D = 501 * r by dsimp [r]; ring]
    apply abs_le.mpr
    constructor <;> linarith
  · rw [show (999 : ℝ) * m / D = 999 * r by dsimp [r]; ring]
    linarith
  · rw [show (1001 : ℝ) * m / D = 1001 * r by dsimp [r]; ring]
    linarith
  · linarith

theorem binaryWellCharges_bit_length {D m : ℕ} (hm : 0 < m) (hscale : 2002 * m ≤ D) :
    Nat.size (binaryPrimaryCharge D m) ≤ 2 * D + 2 ∧
      Nat.size (binarySecondaryCharge D m) ≤ 2 * D + 2 := by
  have h := binaryWellCharges_spec hm hscale
  have hZ : (0 : ℝ) < binaryAmplification D := by exact_mod_cast binaryAmplification_pos D
  have hp : binaryPrimaryCharge D m ≤ binaryAmplification D := by
    have hr : (binaryPrimaryCharge D m : ℝ) ≤ binaryAmplification D :=
      (div_le_one hZ).mp h.2.2.2.1
    exact_mod_cast hr
  have hs : binarySecondaryCharge D m ≤ binaryAmplification D := by
    have hr : (binarySecondaryCharge D m : ℝ) ≤ binaryAmplification D :=
      (div_le_one hZ).mp h.2.2.2.2.2.2.2
    exact_mod_cast hr
  exact ⟨(Nat.size_le_size hp).trans (binaryAmplification_bit_length D),
    (Nat.size_le_size hs).trans (binaryAmplification_bit_length D)⟩

/-- Integer rounding of both actual physical charges preserves the
isolated-well operator estimate uniformly throughout displacement tuning. -/
theorem binary_isolatedPerturbation_bound {D m : ℕ} (hm : 0 < m)
    (hscale : 2002 * m ≤ D) (center displacement : Fin m → Position)
    (hdisp : ∀ j, ‖displacement j‖ ≤ 4) (site : Fin m) (state : Coulomb.H1Vector 1) :
    (∑ spin, ∫ x, ‖(isolatedPerturbation (D : ℝ) (binaryPrimaryRatio D m)
      (binarySecondaryRatio D m) center displacement site (Coulomb.position x 0) : ℂ) *
        state.value spin x‖ ^ 2) ≤
      48 * (1001 * m / (D : ℝ)) ^ 2 * (Coulomb.kinetic state + Coulomb.mass state) := by
  have h := binaryWellCharges_spec hm hscale
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hDlarge : (2002 : ℝ) * m ≤ D := by exact_mod_cast hscale
  have hD : (0 : ℝ) < D := by linarith
  have hr : 0 ≤ (m : ℝ) / D := by positivity
  have hs0 : 0 ≤ binarySecondaryRatio D m :=
    (by positivity : (0 : ℝ) ≤ 999 * m / D).trans h.2.2.2.2.2.1
  apply isolatedPerturbation_small_norm_bound (by linarith : (128 : ℝ) ≤ D)
    h.2.2.1 h.2.2.2.1 hs0 h.2.2.2.2.2.2.2
    (h.2.2.2.2.1.trans _) h.2.2.2.2.2.2.1 _ center displacement hdisp site state
  · simpa only [mul_div_assoc] using
      mul_le_mul_of_nonneg_right (by norm_num : (501 : ℝ) ≤ 1001) hr
  · simpa only [mul_div_assoc] using
      mul_le_mul_of_nonneg_right (by norm_num : (48 : ℝ) ≤ 1001) hr

end
end ContinuumCoulomb

end OAI
