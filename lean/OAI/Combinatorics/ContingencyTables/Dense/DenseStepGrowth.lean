import OAI.Combinatorics.ContingencyTables.Dense.DenseWordProgram

namespace OAI

/-! # Binary size bounds for repeated dense steps on arbitrary input -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms

lemma getD_size_bound (xs : List ℕ) (S i : ℕ)
    (h : ∀ a∈xs,a.size≤S) : (xs.getD i 0).size≤S := by
  by_cases hi : i<xs.length
  · rw [List.getD_eq_getElem xs 0 hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default xs 0 (Nat.le_of_not_gt hi)]
    simp

lemma listExchange_size_bound (xs : List ℕ) (i j S : ℕ)
    (h : ∀ a∈xs,a.size≤S) :
    ∀ a∈listExchange (xs,(i,j)),a.size≤S+2 := by
  intro a ha
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp ha
  have hv := getD_size_bound xs S k h
  have ha : (if k=i then 1 else 0).size≤1 := by split_ifs <;> decide
  have hb := nat_size_add (xs.getD k 0) (if k=i then 1 else 0)
  have hs := Nat.size_le_size (Nat.sub_le
    (xs.getD k 0+(if k=i then 1 else 0)) (if k=j then 1 else 0))
  change (xs.getD k 0+(if k=i then 1 else 0)-(if k=j then 1 else 0)).size≤S+2
  omega

lemma axisListStep_growth (z : AxisData) (ys : List ℕ) (S : ℕ)
    (h : axisListStep z=some ys) (hx : ∀ a∈z.1.1.2,a.size≤S) :
    ys.length=z.1.1.2.length ∧ ∀ a∈ys,a.size≤S+2 := by
  rcases z with ⟨⟨⟨K,xs⟩,i⟩,sign⟩
  by_cases hi : i<xs.length
  · cases sign with
    | false =>
      by_cases hp : 0<xs.getD i 0
      · have he : listExchange (xs,(xs.length,i))=ys := by
          simpa only [axisListStep,hi,ite_true,Bool.false_eq_true,ite_false,hp,
            Option.some.injEq] using h
        rw [←he]
        exact ⟨listExchange_length _,listExchange_size_bound _ _ _ _ hx⟩
      · simp only [axisListStep,hi,ite_true,Bool.false_eq_true,ite_false,hp,
          reduceCtorEq] at h
    | true =>
      by_cases hp : xs.getD i 0+1<K
      · have he : listExchange (xs,(i,xs.length))=ys := by
          simpa only [axisListStep,hi,ite_true,hp,Option.some.injEq] using h
        rw [←he]
        exact ⟨listExchange_length _,listExchange_size_bound _ _ _ _ hx⟩
      · simp only [axisListStep,hi,ite_true,hp,ite_false,reduceCtorEq] at h
  · simp only [axisListStep,hi,ite_false,reduceCtorEq] at h

lemma flatMetropolisStep_growth (z : FlatStepData) (S : ℕ)
    (hx : ∀ a∈z.1.1.2,a.size≤S) :
    (flatMetropolisStep z).length=z.1.1.2.length ∧
      ∀ a∈flatMetropolisStep z,a.size≤S+2 := by
  have hstay : z.1.1.2.length=z.1.1.2.length ∧ ∀ a∈z.1.1.2,a.size≤S+2 :=
    ⟨rfl,fun a ha => (hx a ha).trans (Nat.le_add_right _ _)⟩
  unfold flatMetropolisStep
  cases h : flatStepCandidate z with
  | none => exact hstay
  | some ys =>
    have hy := axisListStep_growth
      (((4*z.1.2^8,z.1.1.2),MatchingFPRAS.StackAddition.value z.2.1/2),
        decide (MatchingFPRAS.StackAddition.value z.2.1%2=1)) ys S h hx
    simp only [Option.elim_some,flatAcceptCandidate]
    split <;> assumption

lemma flatWordStep_growth (z : FlatExponentData×List Bool) (S : ℕ)
    (hx : ∀ a∈z.1.1.2,a.size≤S) :
    (flatWordStep z).length=z.1.1.2.length ∧
      ∀ a∈flatWordStep z,a.size≤S+2 :=
  flatMetropolisStep_growth _ S hx

end ContingencyTables.DensePrograms

end OAI
