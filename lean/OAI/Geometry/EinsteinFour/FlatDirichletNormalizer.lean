import OAI.Geometry.EinsteinFour.FlatDirichletGreenTrace
import OAI.Geometry.EinsteinFour.ScalarNormalizer
import OAI.Geometry.EinsteinFour.SineModeLimit

namespace OAI

/-! The actual square-root normalizer for the flat Green kernel. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem flatDirichlet_posDef (N : ℕ) : (scalarDirichlet N 2).PosDef := by
  apply scalarDirichlet_posDef
  rw [two_sub_two_cos]
  have hx : 0 < firstSineAngle N / 2 := by unfold firstSineAngle; positivity
  have hxπ : firstSineAngle N / 2 < Real.pi := by
    unfold firstSineAngle
    rw [div_div, div_lt_iff₀ (by positivity : (0 : ℝ) < (N + 1) * 2)]
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith [Real.pi_pos]
  exact mul_pos (by norm_num) (sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi hx hxπ))

theorem flatGreen_eq_inverse (N : ℕ) : flatGreen N = (scalarDirichlet N 2)⁻¹ :=
  (Matrix.inv_eq_right_inv (scalarDirichlet_mul_flatGreen N)).symm

theorem flatGreen_posDef (N : ℕ) : (flatGreen N).PosDef := by
  rw [flatGreen_eq_inverse]
  exact (flatDirichlet_posDef N).inv

theorem scaledFlatGreen_posSemidef (t : ℝ) (N : ℕ) : (scaledFlatGreen t N).PosSemidef :=
  (flatGreen_posDef N).posSemidef.smul (sq_nonneg _)

def flatGreenRoot (t : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  (t / (N + 1)) • scalarNormalizer (scalarDirichlet N 2)

theorem flatGreenRoot_square (t : ℝ) (N : ℕ) :
    flatGreenRoot t N * flatGreenRoot t N = scaledFlatGreen t N := by
  rw [flatGreenRoot, scaledFlatGreen, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, ← pow_two, scalarNormalizer_square (flatDirichlet_posDef N),
    ← flatGreen_eq_inverse]

theorem flatGreenRoot_transpose (t : ℝ) (N : ℕ) :
    (flatGreenRoot t N)ᵀ = flatGreenRoot t N := by
  have h := (scalarNormalizer_posSemidef (scalarDirichlet N 2)).isHermitian.eq
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  simp only [flatGreenRoot, Matrix.transpose_smul, h]

end
end PositiveEinsteinFour.Jacobi

end OAI
