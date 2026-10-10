import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace SevenEighths.Probe
noncomputable section

def principalScalar {ι : Type*} (slots : Finset ι) (Z ℓ : ℝ) (S : ι → ℝ) : ℝ :=
  (-1) ^ slots.card * Z ^ (-ℓ / 6) * ∏ i ∈ slots, S i

theorem principalScalar_ne_zero {ι : Type*} (slots : Finset ι)
    {Z ℓ : ℝ} {S : ι → ℝ} (hZ : 0 < Z)
    (hS : ∀ i ∈ slots, 0 < S i) : principalScalar slots Z ℓ S ≠ 0 := by
  unfold principalScalar
  apply mul_ne_zero
  · exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (ne_of_gt (Real.rpow_pos_of_pos hZ _))
  · exact ne_of_gt (Finset.prod_pos hS)

def normalizedProbe (I A : ℝ → ℂ) (c : ℂ) (Z : ℝ) : ℂ := I Z / (c * A Z)

theorem normalizedProbe_error (I A f : ℝ → ℂ) {c : ℂ} {Z : ℝ}
    (hc : c ≠ 0) (hA : A Z ≠ 0) :
    normalizedProbe I A c Z - f Z = (I Z - (c * A Z) * f Z) / (c * A Z) := by
  unfold normalizedProbe
  field_simp

theorem norm_div_bound {I B : ℂ} {Z C D a ε : ℝ} (hZ : 0 < Z)
    (hI : ‖I‖ ≤ C * Z ^ a) (hB : ‖B⁻¹‖ ≤ D * Z ^ ε) :
    ‖I / B‖ ≤ (C * D) * Z ^ (a + ε) := by
  rw [div_eq_mul_inv, norm_mul, Real.rpow_add hZ]
  calc
    ‖I‖ * ‖B⁻¹‖ ≤ (C * Z ^ a) * (D * Z ^ ε) :=
      mul_le_mul hI hB (norm_nonneg _) ((norm_nonneg _).trans hI)
    _ = C * D * (Z ^ a * Z ^ ε) := by ring

theorem common_normalization_bounds (I A f : ℝ → ℂ) {c : ℂ}
    {Z C_low C_high D a b ε : ℝ} (hZ : 0 < Z)
    (hc : c ≠ 0) (hA : A Z ≠ 0)
    (hrecip : ‖(c * A Z)⁻¹‖ ≤ D * Z ^ ε)
    (hlow : ‖I Z‖ ≤ C_low * Z ^ a)
    (hhigh : ‖I Z - (c * A Z) * f Z‖ ≤ C_high * Z ^ b) :
    ‖normalizedProbe I A c Z‖ ≤ (C_low * D) * Z ^ (a + ε) ∧
    ‖normalizedProbe I A c Z - f Z‖ ≤ (C_high * D) * Z ^ (b + ε) := by
  constructor
  · exact norm_div_bound hZ hlow hrecip
  · rw [normalizedProbe_error I A f hc hA]
    exact norm_div_bound hZ hhigh hrecip

end
end SevenEighths.Probe

end OAI
