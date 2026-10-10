import Mathlib
import OAI.Analysis.MatrixSigning.Model
import OAI.Analysis.MatrixSigning.Potential.VarianceH

namespace OAI

open Matrix

namespace CurrentKS
noncomputable section
open Matrix Hermitian State
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {d N : ℕ}
lemma matrix_real_smul_zero (r : ℝ) : r • (0 : Mat d) = 0 := by
  exact smul_zero r
lemma matrix_real_smul_sum (r : ℝ) (f : Fin N → Mat d) :
    r • (∑ i, f i) = ∑ i, r • f i := by
  exact Finset.smul_sum
lemma matrix_real_smul_smul (r s : ℝ) (A : Mat d) :
    r • (s • A) = (r*s) • A := by
  exact smul_smul r s A
lemma opNorm_real_smul (r : ℝ) (A : Mat d) : opNorm (r • A) = |r| * opNorm A := by
  change ‖(r : ℂ) • A‖ = |r| * ‖A‖
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
lemma coe_S (A : Fin N → H d) (x : Coordinates N) :
    ((S A x : H d) : Mat d) = ∑ i,x i • (A i : Mat d) := by
  simp [S]
lemma coe_varianceH (A : Fin N → H d) :
    ((varianceH A : H d) : Mat d) = ∑ i,(A i : Mat d)*(A i : Mat d) := by
  simp [varianceH,sandwich,Hermitian.one]
end
end CurrentKS

end OAI
