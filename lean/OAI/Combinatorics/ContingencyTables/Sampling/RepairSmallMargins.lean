import OAI.Combinatorics.ContingencyTables.Sampling.RepairLargeMass
import OAI.Combinatorics.ContingencyTables.Sampling.SmallCoordinateSums

namespace OAI

/-! # The retained small margins change by at most one under repair -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles SmallContextFibres SmallContextCoordinates PaddedCompletions

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

omit [Fintype J] [LinearOrder I] [LinearOrder J] in
lemma smallQ_column_sum (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (j : J) :
    (∑ i,smallQ small B z i j)=smallColumn small B (smallView small z true) j := by
  unfold smallColumn
  apply Finset.sum_congr rfl
  intro i _
  cases hs : small i j <;> simp [smallQ,smallView,hs]

omit [Fintype I] in
lemma repaired_small_row (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (s t : I×J) (i : I) :
    smallRow small (smallView small (repairedProfile small B z s t) false) i=
      smallRow small (repairMatrix (smallView small z false) s t) i := by
  unfold smallRow
  apply Finset.sum_congr rfl
  intro j _
  cases hs : small i j <;> simp [smallView,repairedProfile,hs]

omit [Fintype J] in
lemma repaired_small_column (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (s t : I×J)
    (hcap : ∀ a : Cells small,repairMatrix (smallView small z false) s t a.val.1 a.val.2 ≤ B a.val.1 a.val.2)
    (j : J) :
    smallColumn small B (smallView small (repairedProfile small B z s t) true) j=
      smallColumnView small (repairMatrix (smallView small z false) s t) j := by
  unfold smallColumn smallColumnView
  apply Finset.sum_congr rfl
  intro i _
  cases hs : small i j
  · simp
  · simp only [hs,ite_true,smallView,dite_eq_left,repairedProfile,ite_true]
    exact Nat.sub_sub_self (hcap ⟨(i,j),hs⟩)

/-- The only loss from a retained margin is the possible single unit
placed into the large receiver. This also covers coincident receiver slots. -/
theorem repair_small_margin_abs (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (s t : I×J)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t)
    (ht : small t.1 t.2=true)
    (hcap : ∀ a : Cells small,repairMatrix (smallView small z false) s t a.val.1 a.val.2 ≤ B a.val.1 a.val.2) :
    (∀ i,|(smallRow small (smallView small (repairedProfile small B z s t) false) i:ℤ)-
      smallRow small (smallView small z false) i| ≤ 1) ∧
    (∀ j,|(smallColumn small B (smallView small (repairedProfile small B z s t) true) j:ℤ)-
      smallColumn small B (smallView small z true) j| ≤ 1) := by
  have hm := repairMatrix_margins hd (fun i => ∑ j,smallView small z false i j)
    (fun j => ∑ i,smallQ small B z i j) (fun _ => rfl) (fun _ => rfl)
  constructor
  · intro i
    rw [repaired_small_row]
    have he := row_small_large small (repairMatrix (smallView small z false) s t) i
    rw [hm.1 i] at he
    dsimp only at he
    rw [← selectedRow_eq small z false i,selectedRow_eq_smallRow] at he
    have hb := repair_large_row_le_one small B z s t hd ht i
    apply abs_le.mpr
    constructor <;> omega
  · intro j
    rw [repaired_small_column small B z s t hcap]
    have he := column_small_large small (repairMatrix (smallView small z false) s t) j
    rw [hm.2 j] at he
    dsimp only at he
    rw [smallQ_column_sum] at he
    have hb := repair_large_column_le_one small B z s t hd ht j
    apply abs_le.mpr
    constructor <;> omega

end ContingencyTables.SmallGraphProfiles

end OAI
