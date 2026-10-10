import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.TraceCLM
import OAI.Analysis.MatrixSigning.Matrices.Sandwich
import OAI.Analysis.MatrixSigning.Matrices.OperatorNorm

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

variable {d N : ℕ}

lemma operatorNorm_square (A : H d) :
    operatorNorm (sandwich A (one : H d))=(operatorNorm A)^2 := by
  let : CStarAlgebra (Mat d) := {}
  have he := A.property.isSelfAdjoint.norm_mul_self
  simpa only [operatorNorm_eq_matrix,sandwich_val,one_val,mul_one] using he

lemma atom_operatorNorm_le_sqrt (A : Fin N → H d) {ν : ℝ} (hν : 0≤ν)
    (hvar : (∑ i,sandwich (A i) (one : H d))≤ν • (one : H d)) (i : Fin N) :
    operatorNorm (A i)≤Real.sqrt ν := by
  have hle : sandwich (A i) (one : H d)≤ν • (one : H d) :=
    (Finset.single_le_sum (fun j _ => psd_nonneg (sandwich_psd (A j) _ one_mem_psdCone))
      (Finset.mem_univ i)).trans hvar
  have hn := operatorNorm_le_of_psd_le (sandwich_psd (A i) _ one_mem_psdCone) hν hle
  rw [operatorNorm_square] at hn
  exact (Real.le_sqrt (operatorNorm_nonneg _) hν).mpr hn

end
end CurrentKS.Hermitian

end OAI
