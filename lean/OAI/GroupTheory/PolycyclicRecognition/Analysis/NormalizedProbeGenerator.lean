import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPivotCancellation

namespace OAI

/-! # Normalizing the neighboring generator at a contact-facet pivot -/

noncomputable section
namespace PolycyclicRecognition

/-- The original sampling slack and the inward displacement of the pivot
add. No fixed positive exponential rate is introduced by normalization. -/
theorem normalized_probe_amplitude_le {t R q c δ r w : ℝ}
    (ht : |t| ≤ R * Real.exp ((1 + δ) * q * r))
    (hw : w = (1 - c * δ) * q * r) :
    |Real.exp (-w) * t| ≤ R * Real.exp (((c + 1) * q) * δ * r) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-w) * (R * Real.exp ((1 + δ) * q * r)) :=
      mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le
    _ = R * Real.exp (-w + (1 + δ) * q * r) := by rw [Real.exp_add]; ring
    _ = _ := by rw [hw]; congr 2; ring

open Module LieAlgebra

variable {L J : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [Fintype J] {a : ℕ} (T : TriangularAdjoint L a)
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

/-- Exact normalized logarithm of one of the actual homogeneous generators. -/
theorem normalized_probe_generator (h : H) (i : Fin M.letterCount) (t : ℝ) :
    cartanIdealWeightDilation T H (-h) (t • M.letter i) =
      (Real.exp (-M.weight i h) * t) • M.letter i := by
  rw [map_smul, cartanIdealWeightDilation_apply_root T H (-h) (M.weight i)
    (M.letter i) (M.letter_root i), smul_smul, map_neg]
  congr 1
  ring

/-- The bound works in any fixed word-coordinate basis, with its fixed
generator norm absorbed into the subexponential radius. -/
theorem normalized_probe_generator_coordinate_le
    (b : Basis J ℝ (cartanRootIdeal H)) (h : H) (i : Fin M.letterCount)
    {t R q c δ r : ℝ}
    (ht : |t| ≤ R * Real.exp ((1 + δ) * q * r))
    (hh : M.weight i h = (1 - c * δ) * q * r) :
    ‖b.equivFun (cartanIdealWeightDilation T H (-h) (t • M.letter i))‖ ≤
      (R * ‖b.equivFun (M.letter i)‖) * Real.exp (((c + 1) * q) * δ * r) := by
  rw [normalized_probe_generator, map_smul, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (normalized_probe_amplitude_le ht hh)
    (norm_nonneg _)).trans_eq (by ring)

end PolycyclicRecognition

end

end OAI
