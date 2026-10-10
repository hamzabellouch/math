import OAI.Analysis.Pureness.Quasitrace.QuasitraceUnitary
import OAI.Analysis.Pureness.Quasitrace.QuasitraceMatrixDiagonal
import Mathlib.Analysis.Matrix.Spectrum

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped NNReal ENNReal ComplexOrder ComplexStarModule
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma realDiagonal_eq_sum (d : ι → ℝ) :
    CStarMatrix.ofMatrix (Matrix.diagonal (fun i => (d i : ℂ))) =
      ∑ i, d i • (matrixCorner i (1 : ℂ)) := by
  have he := congrArg CStarMatrix.ofMatrixStarAlgEquiv
    (Matrix.sum_single_eq_diagonal (fun i => (d i : ℂ)))
  rw [map_sum] at he
  change CStarMatrix.ofMatrixStarAlgEquiv (Matrix.diagonal (fun i => (d i : ℂ))) = _
  rw [← he]
  apply Finset.sum_congr rfl
  intro i _
  apply CStarMatrix.ext
  intro j k
  change Matrix.single i i (d i : ℂ) j k = (d i) • (Matrix.single i i (1 : ℂ) j k)
  by_cases hj : i=j <;> by_cases hk : i=k <;>
    simp [Matrix.single, hj, hk]

lemma positiveQuasitrace_realDiagonal (T : PositiveQuasitrace (CStarMatrix ι ι ℂ))
    (i : ι) (d : ι → ℝ) :
    T.complexValue (CStarMatrix.ofMatrix (Matrix.diagonal (fun j => (d j : ℂ)))) =
      (∑ j, (d j : ℂ)) * (T (Positive.map (matrixCorner i) ⟨1,zero_le_one⟩) : ℂ) := by
  let p (j : ι) : Positive (CStarMatrix ι ι ℂ) := Positive.map (matrixCorner j) ⟨1,zero_le_one⟩
  let a (j : ι) : selfAdjoint (CStarMatrix ι ι ℂ) := d j • ⟨(p j).1,(p j).2.isSelfAdjoint⟩
  have hc : ∀ j ∈ (Finset.univ : Finset ι), ∀ k ∈ (Finset.univ : Finset ι),
      Commute (a j).1 (a k).1 := by
    intro j _ k _
    apply Commute.smul_left
    apply Commute.smul_right
    by_cases hjk : j=k
    · subst k; exact Commute.refl _
    · change singleMatrix j j (1 : ℂ) * singleMatrix k k 1 = singleMatrix k k 1 * singleMatrix j j 1
      rw [singleMatrix_mul_ne _ _ _ _ hjk, singleMatrix_mul_ne _ _ _ _ (Ne.symm hjk)]
  have he : CStarMatrix.ofMatrix (Matrix.diagonal (fun j => (d j : ℂ))) = (∑ j, a j).1 :=
    by
      change _ = (selfAdjoint (CStarMatrix ι ι ℂ)).subtype (∑ j, a j)
      rw [map_sum]
      exact realDiagonal_eq_sum d
  rw [he,T.complexValue_selfAdjoint,T.selfAdjointValue_sum _ _ hc]
  rw [Complex.ofReal_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  have hj := T.selfAdjointValue_smul (d j) ⟨(p j).1, (p j).2.isSelfAdjoint⟩
  change T.selfAdjointValue (a j) = _ at hj
  rw [hj, T.selfAdjointValue_positive (p j), Complex.ofReal_mul]
  rw [positiveQuasitrace_matrixCorner_eq T j i]

lemma positiveQuasitrace_scalarMatrix_selfAdjoint
    (T : PositiveQuasitrace (CStarMatrix ι ι ℂ)) (i : ι)
    (a : selfAdjoint (CStarMatrix ι ι ℂ)) :
    T.complexValue a.1 = Matrix.trace (CStarMatrix.ofMatrix.symm a.1) *
      (T (Positive.map (matrixCorner i) ⟨1,zero_le_one⟩) : ℂ) := by
  let M := CStarMatrix.ofMatrix.symm a.1
  have hM : M.IsHermitian := a.2
  let u : unitary (CStarMatrix ι ι ℂ) :=
    ⟨CStarMatrix.ofMatrix hM.eigenvectorUnitary,
      Unitary.map_mem CStarMatrix.ofMatrixStarAlgEquiv hM.eigenvectorUnitary.2⟩
  have he : a.1 = Unitary.conjStarAlgAut ℂ _ u
      (CStarMatrix.ofMatrix (Matrix.diagonal (fun j => (hM.eigenvalues j : ℂ)))) := by
    exact congrArg CStarMatrix.ofMatrix hM.spectral_theorem
  conv_lhs => rw [he,T.complexValue_unitary_conjugate,positiveQuasitrace_realDiagonal T i]
  rw [hM.trace_eq_sum_eigenvalues]
  rfl

theorem positiveQuasitrace_scalarMatrix_complex
    (T : PositiveQuasitrace (CStarMatrix ι ι ℂ)) (i : ι) (x : CStarMatrix ι ι ℂ) :
    T.complexValue x = Matrix.trace (CStarMatrix.ofMatrix.symm x) *
      (T (Positive.map (matrixCorner i) ⟨1,zero_le_one⟩) : ℂ) := by
  have hr := positiveQuasitrace_scalarMatrix_selfAdjoint T i (ℜ x)
  have hi := positiveQuasitrace_scalarMatrix_selfAdjoint T i (ℑ x)
  rw [T.complexValue_selfAdjoint] at hr hi
  unfold PositiveQuasitrace.complexValue
  rw [hr,hi]
  have he : Matrix.trace (CStarMatrix.ofMatrix.symm x) =
      Matrix.trace (CStarMatrix.ofMatrix.symm (ℜ x).1) +
        Complex.I * Matrix.trace (CStarMatrix.ofMatrix.symm (ℑ x).1) := by
    have hx := realPart_add_I_smul_imaginaryPart x
    have hh := congrArg (fun z : CStarMatrix ι ι ℂ => Matrix.trace (CStarMatrix.ofMatrix.symm z)) hx
    change Matrix.trace (CStarMatrix.ofMatrix.symm (ℜ x).1 +
      Complex.I • CStarMatrix.ofMatrix.symm (ℑ x).1) = _ at hh
    simpa only [Matrix.trace_add, Matrix.trace_smul, smul_eq_mul] using hh.symm
  rw [he]
  ring
end CuntzPureness

end

end OAI
