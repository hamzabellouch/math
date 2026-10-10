import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.Sandwich2
import OAI.Analysis.MatrixSigning.Matrices.JordanCLM

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma jordanCLM_strict_pos [NeZero d] (A B : H d) (hA : A ∈ pd d) (hB : B ∈ pd d)
    (U : H d) (hU : U ≠ 0) : 0 < inner ℝ U (jordanCLM A B U) := by
  rw [jordanCLM_quadratic]
  apply mul_pos (by norm_num)
  have hn := inner_nonneg_of_psd B (sandwich U A) hB.posSemidef
    (sandwich_psd U A hA.posSemidef)
  apply lt_of_le_of_ne hn
  intro he
  have hz := eq_zero_of_inner_pd hB (sandwich_psd U A hA.posSemidef) he.symm
  exact hU ((sandwich_eq_zero_iff U A hA).mp hz)

end
end CurrentKS.Hermitian

end OAI
