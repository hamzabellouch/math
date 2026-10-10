import OAI.Combinatorics.ContingencyTables.Sampling.ExactMatrixTrial
import OAI.Combinatorics.ContingencyTables.Sampling.OriginalBoxLaw

namespace OAI

/-! # Feasibility of every decoded candidate in the exact branch -/

namespace ContingencyTables.ExactMatrixTrial
open ProfilePrograms DensePrograms OriginalTableBox
open scoped BigOperators Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

lemma lookup_index (fallback X : Table r c) :
    lookup ((originalCandidates (List.ofFn r,List.ofFn c),matrixCode fallback.val),
      (index r c le_rfl X).val)=matrixCode X.val := by
  rw [lookup,candidates_code]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,Fin.isLt,dite_true,Option.getD_some]
  rw [OriginalBoxLaw.tableAt_index]
  rfl

/-- Even a malformed index returns the fixed feasible fallback. -/
lemma lookup_feasible (fallback : Table r c) (i : ℕ) :
    ∃ X : Table r c,
      lookup ((originalCandidates (List.ofFn r,List.ofFn c),matrixCode fallback.val),i)=
        matrixCode X.val := by
  rw [lookup,candidates_code]
  by_cases hi : i<((∑ j,r j)+1)^(m*n)
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi,dite_true,Option.getD_some]
    cases hx : tableAt r c (⟨i,hi⟩ : Index m n (∑ j,r j)) with
    | none => exact ⟨fallback,rfl⟩
    | some X => exact ⟨X,rfl⟩
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi,dite_false,Option.getD_none]
    exact ⟨fallback,rfl⟩

end
end ContingencyTables.ExactMatrixTrial

end OAI
