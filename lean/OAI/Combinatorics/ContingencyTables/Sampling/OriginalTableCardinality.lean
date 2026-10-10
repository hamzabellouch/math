import OAI.Combinatorics.ContingencyTables.Sampling.OriginalTableBox
import OAI.Combinatorics.ContingencyTables.Machines.FirstSuccessProgram

namespace OAI

/-! # Computing the number of feasible original-table box entries -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

def originalCardEntry (o : Option MatrixCode) : ℕ := if o.isSome then 1 else 0

def originalCardEntryRealizer : Realizer originalCardEntry :=
  choose FirstSuccessProgram.isSomeRealizer (constant 1) (constant 0)

lemma polynomial_originalCardEntry : PolynomialTime originalCardEntryRealizer :=
  polynomial_choose FirstSuccessProgram.polynomial_isSome (polynomial_constant 1) (polynomial_constant 0)

def originalCardinality (z : CompletionMargins) : ℕ :=
  ((originalCandidates z).map originalCardEntry).sum

def originalCardinalityRealizer : Realizer originalCardinality :=
  composition (f := originalCandidates) (g := fun xs => (xs.map originalCardEntry).sum)
    originalCandidatesRealizer (composition (map originalCardEntryRealizer) listSum)

lemma work_originalCardinality : WorkBound originalCardinalityRealizer originalEnumerationMeasure := by
  unfold originalCardinalityRealizer
  exact work_then_polynomial work_originalCandidates
    (polynomial_composition (polynomial_map polynomial_originalCardEntry) polynomial_listSum)

lemma originalCardinality_actual {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) :
    originalCardinality (List.ofFn r,List.ofFn c)=Fintype.card (Table r c) := by
  classical
  unfold originalCardinality
  rw [OriginalTableBox.candidates_code,List.map_ofFn,List.sum_ofFn]
  dsimp only [Function.comp_apply]
  have he (k : OriginalTableBox.Index m n (∑ i,r i)) :
      originalCardEntry ((OriginalTableBox.tableAt r c k).map (fun T => matrixCode T.val))=
        ∑ T : Table r c,if OriginalTableBox.tableAt r c k=some T then 1 else 0 := by
    cases hh : OriginalTableBox.tableAt r c k <;> simp [originalCardEntry]
  simp_rw [he]
  rw [Finset.sum_comm]
  simp_rw [OriginalTableBox.tableAt_eq_some r c le_rfl]
  have hl : (∑ T : Table r c,∑ k : OriginalTableBox.Index m n (∑ i,r i),
      if OriginalTableBox.index r c le_rfl T=k then 1 else 0)=Fintype.card (Table r c) := by simp
  exact hl

end ContingencyTables.ProfilePrograms

end OAI
