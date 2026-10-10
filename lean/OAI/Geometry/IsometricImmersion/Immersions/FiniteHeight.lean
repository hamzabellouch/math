import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
namespace SmoothLocal

theorem det_two_smul (B : Matrix (Fin 2) (Fin 2) ℝ) (ν : ℝ) :
    (ν • B).det = ν ^ 2 * B.det := by
  simp

section Inner
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem normal_remainder_orthogonal (e n : V) (hn : inner ℝ n n = 1) :
    inner ℝ (e - (inner ℝ n e) • n) n = 0 := by
  rw [inner_sub_left, real_inner_smul_left, hn, mul_one, real_inner_comm e n]
  exact sub_self _

theorem normal_tangent_identity (e n : V) (hn : inner ℝ n n = 1) :
    inner ℝ (e - (inner ℝ n e) • n) (e - (inner ℝ n e) • n) +
      (inner ℝ n e) ^ 2 = inner ℝ e e := by
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, hn]
  rw [real_inner_comm e n]
  ring

end Inner
end SmoothLocal

end

end OAI
