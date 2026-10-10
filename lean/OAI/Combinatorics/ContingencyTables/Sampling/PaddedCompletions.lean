import OAI.Combinatorics.ContingencyTables.Transport.RowColumnPenalties

namespace OAI

/-!
# Zero penalties are exactly padded residual completions

Retain the small x,y views and fill every large cell with the balanced
pair (A,B-A). For an assignment supported on large cells, the full margin
equations are precisely the padded residual margin equations. The small
positive-part penalties enforce the original nonnegative residual tests.
-/

namespace ContingencyTables.PaddedCompletions

open scoped BigOperators Classical
open RowColumnPenalties NestedPenaltyApplication BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def smallRow (small : I → J → Bool) (X : I → J → ℕ) (i : I) : ℕ :=
  ∑ j, if small i j then X i j else 0

noncomputable def smallColumn (small : I → J → Bool) (B Y : I → J → ℕ) (j : J) : ℕ :=
  ∑ i, if small i j then B i j-Y i j else 0

noncomputable def rowLargeCount (small : I → J → Bool) (i : I) : ℕ :=
  ∑ j, if small i j then 0 else 1

noncomputable def columnLargeCount (small : I → J → Bool) (j : J) : ℕ :=
  ∑ i, if small i j then 0 else 1

def profile (small : I → J → Bool) (B X Y A : I → J → ℕ) : ((I × J) × Bool) → ℕ :=
  fun u => if u.2 then (if small u.1.1 u.1.2 then Y u.1.1 u.1.2 else B u.1.1 u.1.2-A u.1.1 u.1.2)
    else (if small u.1.1 u.1.2 then X u.1.1 u.1.2 else A u.1.1 u.1.2)

def Supported (small : I → J → Bool) (A : I → J → ℕ) : Prop :=
  ∀ i j, small i j=true → A i j=0

def OriginalResidualsNonnegative (small : I → J → Bool) (B X Y : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) : Prop :=
  (∀ i, smallRow small X i ≤ r i) ∧ (∀ j, smallColumn small B Y j ≤ c j)

omit [Fintype I] [Fintype J] in
lemma profile_inBox (small : I → J → Bool) (B X Y A : I → J → ℕ)
    (hX : ∀ i j, small i j=true → X i j ≤ B i j)
    (hY : ∀ i j, small i j=true → Y i j ≤ B i j)
    (hA : ∀ i j, small i j=false → A i j ≤ B i j) :
    InBox (fun u => B u.1.1 u.1.2) (profile small B X Y A) := by
  rintro ⟨⟨i,j⟩,t⟩
  cases t <;> cases hs : small i j <;> simp only [profile,hs,ite_true]
  · exact hA i j hs
  · exact hX i j hs
  · exact Nat.sub_le _ _
  · exact hY i j hs

omit [Fintype I] in
lemma profile_row (small : I → J → Bool) (B X Y A : I → J → ℕ)
    (hA : Supported small A) (i : I) :
    (∑ j, rowView (profile small B X Y A) i j)=smallRow small X i+∑ j, A i j := by
  unfold smallRow
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  cases hs : small i j
  · simp [rowView,profile,hs]
  · simp [rowView,profile,hs,hA i j hs]

omit [Fintype J] in
lemma profile_column (small : I → J → Bool) (B X Y A : I → J → ℕ)
    (hA : Supported small A) (hcap : ∀ i j, small i j=false → A i j ≤ B i j) (j : J) :
    (∑ i, columnView B (profile small B X Y A) i j)=smallColumn small B Y j+∑ i, A i j := by
  unfold smallColumn
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hs : small i j
  · simpa [columnView,profile,hs] using Nat.sub_sub_self (hcap i j hs)
  · simp [columnView,profile,hs,hA i j hs]

omit [Fintype I] in
lemma profile_small_row (small : I → J → Bool) (B X Y A : I → J → ℕ) (i : I) :
    (∑ j, if small i j then rowView (profile small B X Y A) i j else 0)=smallRow small X i := by
  apply Finset.sum_congr rfl
  intro j _
  cases hs : small i j <;> simp [rowView,profile,hs]

omit [Fintype J] in
lemma profile_small_column (small : I → J → Bool) (B X Y A : I → J → ℕ) (j : J) :
    (∑ i, if small i j then columnView B (profile small B X Y A) i j else 0)=smallColumn small B Y j := by
  apply Finset.sum_congr rfl
  intro i _
  cases hs : small i j <;> simp [columnView,profile,hs]

/-- No positivity or balance assumption is imposed on the retained
small profile. Thus this exact identity covers transversals and defects. -/
theorem zero_penalty_iff_padded_completion (small : I → J → Bool) (B X Y A : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (hA : Supported small A)
    (hX : ∀ i j, small i j=true → X i j ≤ B i j)
    (hY : ∀ i j, small i j=true → Y i j ≤ B i j)
    (hcap : ∀ i j, small i j=false → A i j ≤ B i j) :
    penalty RowColumnPenalties.cellLine (smallCoordinate small)
      (fullOffset B (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L))
      viewSlope (smallOffset small B r c) viewSlope (profile small B X Y A)=0 ↔
      OriginalResidualsNonnegative small B X Y r c ∧
        HasMargins A (fun i => r i-smallRow small X i+rowLargeCount small i*L)
          (fun j => c j-smallColumn small B Y j+columnLargeCount small j*L) := by
  rw [penalty_zero_iff small B r _ c _ _ (profile_inBox small B X Y A hX hY hcap)]
  simp only [FullConditions,profile_row small B X Y A hA,profile_column small B X Y A hA hcap,
    profile_small_row,profile_small_column,OriginalResidualsNonnegative,HasMargins]
  constructor
  · rintro ⟨hr,hc,hsr,hsc⟩
    refine ⟨⟨hsr,hsc⟩,?_,?_⟩
    · intro i; have h := hr i; have hs := hsr i; omega
    · intro j; have h := hc j; have hs := hsc j; omega
  · rintro ⟨⟨hsr,hsc⟩,hr,hc⟩
    refine ⟨?_,?_,hsr,hsc⟩
    · intro i; have h := hr i; have hs := hsr i; omega
    · intro j; have h := hc j; have hs := hsc j; omega

end ContingencyTables.PaddedCompletions

end OAI
