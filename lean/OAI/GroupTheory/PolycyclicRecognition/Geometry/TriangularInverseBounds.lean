import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularWordBounds

namespace OAI

/-!
# Polynomial inverse bounds in bounded-height triangular regions

Removing the diagonal leaves a unipotent matrix. Its inverse is a finite
geometric sum, so a bound for the matrix and its height gives a polynomial
bound for its inverse. Both bounds are needed when turning coordinate packing
into packing for a left invariant group metric.
-/

namespace PolycyclicRecognition.PositiveTriangular

open scoped Matrix.Norms.Operator

variable {n : ℕ} [NeZero n]

theorem norm_inverse_le (g : positiveTriangular n) {H P : ℝ}
    (hP : 0 ≤ P) (hg : ‖matrix g‖ ≤ P) (hheight : ‖(height g).toAdd‖ ≤ H) :
    ‖matrix g⁻¹‖ ≤ Real.exp H * ((n : ℝ) * (1 + (1 + P * Real.exp H)) ^ n) := by
  let u : (Matrix (Fin n) (Fin n) ℝ)ˣ := g.val * (frame g)⁻¹
  have hframe := frame_norm_le_exp g hheight
  have hstrict : StrictUpper ((u : Matrix (Fin n) (Fin n) ℝ) - 1) := by
    have h := strictUpper_diagonal_gauge (matrix g) (upper g)
      (diagonal (1 : positiveTriangular n)) (diagonal g) (by
        intro i
        simp only [map_one, Pi.one_apply, Units.val_one, one_mul, diagonal_val])
    change StrictUpper ((frame (1 : positiveTriangular n) : Matrix (Fin n) (Fin n) ℝ) * matrix g *
      (↑(frame g)⁻¹ : Matrix (Fin n) (Fin n) ℝ) - 1) at h
    simpa only [u, Units.val_mul, frame_one, Units.val_one, one_mul] using h
  have hn : (1 - (u : Matrix (Fin n) (Fin n) ℝ)) ^ n = 0 := by
    apply StrictUpper.pow_eq_zero
    intro i j hij
    have hs := hstrict i j hij
    change (u : Matrix (Fin n) (Fin n) ℝ) i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j = 0 at hs
    change (1 : Matrix (Fin n) (Fin n) ℝ) i j - (u : Matrix (Fin n) (Fin n) ℝ) i j = 0
    linarith
  have hnormu : ‖(u : Matrix (Fin n) (Fin n) ℝ)‖ ≤ P * Real.exp H :=
    (norm_mul_le _ _).trans (mul_le_mul hg hframe.2 (norm_nonneg _) hP)
  have hnorm : ‖1 - (u : Matrix (Fin n) (Fin n) ℝ)‖ ≤ 1 + P * Real.exp H := by
    exact (norm_sub_le _ _).trans (by simpa only [norm_one] using add_le_add le_rfl hnormu)
  have hinv : ‖(↑u⁻¹ : Matrix (Fin n) (Fin n) ℝ)‖ ≤
      (n : ℝ) * (1 + (1 + P * Real.exp H)) ^ n := by
    apply (norm_inv_le_of_nilpotent_sub_one u n hn).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply pow_le_pow_left₀ (by positivity)
    exact add_le_add le_rfl hnorm
  have heq : g.val⁻¹ = (frame g)⁻¹ * u⁻¹ := by simp [u]
  change ‖(↑(g.val⁻¹) : Matrix (Fin n) (Fin n) ℝ)‖ ≤ _
  rw [heq, Units.val_mul]
  exact (norm_mul_le _ _).trans (mul_le_mul hframe.2 hinv (norm_nonneg _) (Real.exp_pos H).le)

end PolycyclicRecognition.PositiveTriangular

end OAI
