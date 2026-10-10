import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.PivotRowCorrectness
import OAI.Analysis.MatrixSigning.Matrices.PivotDecisionMachine
import OAI.Analysis.MatrixSigning.Matrices.UniformEliminationHeight

namespace OAI

section

namespace KS.W17.PivotDecision
open KS.W07

private theorem noIndex {n : ℕ} (M : DenseRatMatrix (n+1))
    (h : firstNonzeroOffDiagonal (DenseRatMatrix.decode M) = none) :
    (PivotRowLoop.outcome M 1 n).found = false := by
  have he := PivotRowLoop.offDiagonal_outcome M
  rw [h] at he
  cases hf : (PivotRowLoop.outcome M 1 n).found
  · rfl
  · simp [PivotRowLoop.foundIndex,hf] at he

private theorem some_index {n : ℕ} (M : DenseRatMatrix (n+1)) (j : Fin n)
    (h : firstNonzeroOffDiagonal (DenseRatMatrix.decode M) = some j) :
    (PivotRowLoop.outcome M 1 n).found = true ∧ (PivotRowLoop.outcome M 1 n).index = j.succ.val := by
  have he := PivotRowLoop.offDiagonal_outcome M
  rw [h] at he
  cases hf : (PivotRowLoop.outcome M 1 n).found
  · simp [PivotRowLoop.foundIndex,hf] at he
  · refine ⟨rfl,?_⟩
    simpa [PivotRowLoop.foundIndex,hf] using he

theorem result_nonterminal {n : ℕ} (M : DenseRatMatrix (n+1))
    (ht : pivotTerminal (DenseRatMatrix.decode M) = none) :
    result M = PivotRowLoop.initial M := by
  rcases pivotTerminal_none_cases (DenseRatMatrix.decode M) ht with ⟨hz,hr⟩ | hp
  · have hf := noIndex M hr
    funext j
    simp [result,hz,PivotRowLoop.finished,hf,PivotRowLoop.initial,PivotRowLoop.state,
      Computability.encodeNat,Computability.encodeNum]
  · have hz := hp.ne'
    have hn := not_lt.mpr hp.le
    funext j
    by_cases hj : j = 29 <;>
      simp [result,hz,KS.W06.RationalSignClassifier.outputCode,hn,
        PivotRowLoop.initial,PivotRowLoop.state,Function.update,hj]

theorem result_negative {n : ℕ} (M : DenseRatMatrix (n+1))
    (hn : DenseRatMatrix.decode M 0 0 < 0) :
    result M = Function.update (PivotRowLoop.initial M) 29 [false] := by
  simp [result,hn.ne,KS.W06.RationalSignClassifier.outputCode,hn]

theorem result_sparse {n : ℕ} (M : DenseRatMatrix (n+1)) (j : Fin n)
    (hz : DenseRatMatrix.decode M 0 0 = 0)
    (hj : firstNonzeroOffDiagonal (DenseRatMatrix.decode M) = some j) :
    result M = PivotRowLoop.finished M j.succ.val true := by
  obtain ⟨hf,hi⟩ := some_index M j hj
  simp [result,hz,hf,hi]

end KS.W17.PivotDecision

end

end OAI
