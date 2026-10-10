import OAI.Combinatorics.ContingencyTables.Sampling.SmallProfileRepair

namespace OAI

/-! # A repair adds at most one unit outside the retained small cells -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles SmallContextFibres PaddedCompletions

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

omit [Fintype I] [Fintype J] in
lemma repair_large_value (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (s t : I×J)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t)
    (ht : small t.1 t.2=true) (i : I) (j : J) (hij : small i j=false) :
    repairMatrix (smallView small z false) s t i j = if i=t.1 ∧ j=s.2 then 1 else 0 := by
  have hne : ¬(i=t.1 ∧ j=t.2) := by
    rintro ⟨rfl,rfl⟩
    rw [ht] at hij
    contradiction
  have he := repairMatrix_cast hd i j
  have hz : smallView small z false i j=0 := by simp [smallView,hij]
  simp only [transferInt,hz,ite_eq_right hne,Nat.cast_zero,sub_zero,zero_add] at he
  split_ifs at he ⊢ <;> omega

omit [Fintype I] in
lemma repair_large_row_le_one (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (s t : I×J)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t)
    (ht : small t.1 t.2=true) (i : I) :
    largeRow small (repairMatrix (smallView small z false) s t) i ≤ 1 := by
  unfold largeRow
  calc
    _ ≤ ∑ j : J,if j=s.2 then 1 else 0 := by
      apply Finset.sum_le_sum
      intro j _
      cases hs : small i j
      · rw [ite_eq_right Bool.false_ne_true,repair_large_value small B z s t hd ht i j hs]
        split_ifs <;> simp_all
      · simp only [ite_true]
        split_ifs <;> simp_all
    _ = _ := by simp

omit [Fintype J] in
lemma repair_large_column_le_one (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (s t : I×J)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t)
    (ht : small t.1 t.2=true) (j : J) :
    largeColumnView small (repairMatrix (smallView small z false) s t) j ≤ 1 := by
  unfold largeColumnView
  calc
    _ ≤ ∑ i : I,if i=t.1 then 1 else 0 := by
      apply Finset.sum_le_sum
      intro i _
      cases hs : small i j
      · rw [ite_eq_right Bool.false_ne_true,repair_large_value small B z s t hd ht i j hs]
        split_ifs <;> simp_all
      · simp only [ite_true]
        split_ifs <;> simp_all
    _ = _ := by simp

end ContingencyTables.SmallGraphProfiles

end OAI
