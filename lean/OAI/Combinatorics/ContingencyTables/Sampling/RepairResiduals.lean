import OAI.Combinatorics.ContingencyTables.Sampling.RepairPrefixes
import OAI.Combinatorics.ContingencyTables.Transport.CompletionCounts

namespace OAI

/-! # Original residual bounds are preserved by the literal repair

Only a small source entry is lowered. Every large entry is unchanged or
increased. Since full row and column-view totals are preserved, the
small row/column sums cannot increase.
-/

namespace ContingencyTables

open scoped BigOperators Classical
open PaddedCompletions CompletionCounts

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

noncomputable def largeRow (small : I → J → Bool) (X : I → J → ℕ) (i : I) : ℕ :=
  ∑ j, if small i j then 0 else X i j

noncomputable def smallColumnView (small : I → J → Bool) (Q : I → J → ℕ) (j : J) : ℕ :=
  ∑ i, if small i j then Q i j else 0

noncomputable def largeColumnView (small : I → J → Bool) (Q : I → J → ℕ) (j : J) : ℕ :=
  ∑ i, if small i j then 0 else Q i j

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
lemma row_small_large (small : I → J → Bool) (X : I → J → ℕ) (i : I) :
    smallRow small X i+largeRow small X i=∑ j, X i j := by
  unfold smallRow largeRow
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  cases small i j <;> simp

omit [Fintype J] [DecidableEq I] [DecidableEq J] in
lemma column_small_large (small : I → J → Bool) (Q : I → J → ℕ) (j : J) :
    smallColumnView small Q j+largeColumnView small Q j=∑ i, Q i j := by
  unfold smallColumnView largeColumnView
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases small i j <;> simp

omit [Fintype I] [Fintype J] in
lemma repairMatrix_large {small : I → J → Bool} {x q : I → J → ℕ} {s t : I×J}
    (h : IsDefect x q s t) (hs : small s.1 s.2=true) (ht : small t.1 t.2=true)
    (i : I) (j : J) (hij : small i j=false) :
    q i j=x i j ∧ x i j ≤ repairMatrix x s t i j := by
  have hne (w : I×J) (hw : small w.1 w.2=true) : ¬(i=w.1 ∧ j=w.2) := by
    rintro ⟨rfl,rfl⟩
    rw [hw] at hij
    contradiction
  have hst := hne s hs
  have htt := hne t ht
  constructor
  · apply Int.natCast_inj.mp
    rw [h.2]
    simp only [transferInt,hst,htt,↓reduceIte,sub_zero,add_zero]
  · have he := repairMatrix_cast h i j
    simp only [transferInt,htt,↓reduceIte,sub_zero] at he
    split_ifs at he <;> omega

/-- This covers small and large receivers and the two possible receiver
coincidences without a special case in the residual calculation. -/
theorem repairMatrix_small_sums {small : I → J → Bool} {x q : I → J → ℕ} {s t : I×J}
    (h : IsDefect x q s t) (hs : small s.1 s.2=true) (ht : small t.1 t.2=true) :
    (∀ i, smallRow small (repairMatrix x s t) i ≤ smallRow small x i) ∧
      (∀ j, smallColumnView small (repairMatrix x s t) j ≤ smallColumnView small q j) := by
  have hm := repairMatrix_margins h (fun i => ∑ j, x i j) (fun j => ∑ i, q i j)
    (fun _ => rfl) (fun _ => rfl)
  constructor
  · intro i
    have hlarge : largeRow small x i ≤ largeRow small (repairMatrix x s t) i := by
      apply Finset.sum_le_sum
      intro j _
      cases hij : small i j
      · exact (repairMatrix_large h hs ht i j hij).2
      · exact le_rfl
    have h0 := row_small_large small x i
    have h1 := row_small_large small (repairMatrix x s t) i
    rw [hm.1] at h1
    dsimp only at h1
    omega
  · intro j
    have hlarge : largeColumnView small q j ≤ largeColumnView small (repairMatrix x s t) j := by
      apply Finset.sum_le_sum
      intro i _
      cases hij : small i j
      · obtain ⟨he,hge⟩ := repairMatrix_large h hs ht i j hij
        simpa [he] using hge
      · exact le_rfl
    have h0 := column_small_large small q j
    have h1 := column_small_large small (repairMatrix x s t) j
    rw [hm.2] at h1
    dsimp only at h1
    omega

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
lemma entry_le_smallRow (small : I → J → Bool) (X : I → J → ℕ) (i : I) (j : J)
    (hij : small i j=true) : X i j ≤ smallRow small X i := by
  have h := Finset.single_le_sum (fun k _ => Nat.zero_le (if small i k then X i k else 0))
    (Finset.mem_univ j)
  simpa only [smallRow,smallColumnView,hij,↓reduceIte] using h

omit [Fintype J] [DecidableEq I] [DecidableEq J] in
lemma entry_le_smallColumn (small : I → J → Bool) (Q : I → J → ℕ) (i : I) (j : J)
    (hij : small i j=true) : Q i j ≤ smallColumnView small Q j := by
  have h := Finset.single_le_sum (fun k _ => Nat.zero_le (if small k j then Q k j else 0))
    (Finset.mem_univ i)
  simpa only [smallRow,smallColumnView,hij,↓reduceIte] using h

/-- Every repaired small cell respects the manuscript's actual U box,
because one of its original incident margins is strictly below U. -/
theorem repairMatrix_small_capacity {x q : I → J → ℕ} {s t : I×J}
    (r : I → ℕ) (c : J → ℕ) (U : ℕ) (h : IsDefect x q s t)
    (hs : firstPaperSmall r c U s.1 s.2=true) (ht : firstPaperSmall r c U t.1 t.2=true)
    (hr : ∀ i, smallRow (firstPaperSmall r c U) x i ≤ r i)
    (hc : ∀ j, smallColumnView (firstPaperSmall r c U) q j ≤ c j)
    (i : I) (j : J) (hij : firstPaperSmall r c U i j=true) :
    repairMatrix x s t i j < U := by
  obtain ⟨hrow,hcol⟩ := repairMatrix_small_sums h hs ht
  have h1 := (entry_le_smallRow _ (repairMatrix x s t) i j hij).trans ((hrow i).trans (hr i))
  have h2 := (entry_le_smallColumn _ (repairMatrix x s t) i j hij).trans ((hcol j).trans (hc j))
  have hinc : r i<U ∨ c j<U := by simpa only [firstPaperSmall,decide_eq_true_eq] using hij
  rcases hinc with hinc|hinc
  · exact h1.trans_lt hinc
  · exact h2.trans_lt hinc

end ContingencyTables

end OAI
