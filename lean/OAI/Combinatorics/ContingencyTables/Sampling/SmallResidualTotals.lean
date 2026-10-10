import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperFeasibility

namespace OAI

/-! # Conservation makes the residual-total test redundant -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open SmallContextFibres FirstPaperProfiles PaddedCompletions CompletionCounts
open FirstPaperPhysicalMarginal PhysicalCompletionFibres

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma pattern_view_totals (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (hz : Pattern small B z) :
    (∑ i,∑ j,smallView small z false i j)=∑ i,∑ j,smallQ small B z i j := by
  rcases hz with h|⟨s,t,_,_,h⟩
  · change ∀ i j,smallView small z false i j=smallQ small B z i j at h
    simp_rw [h]
  · apply Int.natCast_inj.mp
    simp only [Nat.cast_sum]
    symm
    simp_rw [h.2,transferInt]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,ite_and]
    simp

lemma pattern_small_totals (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (hz : Pattern small B z) :
    (∑ i,smallRow small (smallView small z false) i)=
      ∑ j,smallColumn small B (smallView small z true) j := by
  have hrow (i : I) : smallRow small (smallView small z false) i=
      ∑ j,smallView small z false i j := by
    unfold smallRow
    apply Finset.sum_congr rfl
    intro j _
    by_cases hs : small i j=true
    · simp only [hs,ite_true]
    · simp [smallView,hs]
  have hcol (j : J) : smallColumn small B (smallView small z true) j=
      ∑ i,smallQ small B z i j := by
    unfold smallColumn
    apply Finset.sum_congr rfl
    intro i _
    by_cases hs : small i j=true <;> simp [smallQ,smallView,hs]
  simp_rw [hrow,hcol]
  exact (pattern_view_totals small B z hz).trans Finset.sum_comm

lemma padded_residual_totals (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) (hz : Pattern small B z)
    (hr : ∀ i,smallRow small (smallView small z false) i≤r i)
    (hc : ∀ j,smallColumn small B (smallView small z true) j≤c j) :
    (∑ i,((r i-smallRow small (smallView small z false) i)+rowLargeCount small i*L))=
      ∑ j,((c j-smallColumn small B (smallView small z true) j)+columnLargeCount small j*L) := by
  have hs := pattern_small_totals small B z hz
  have hlarge : (∑ i,rowLargeCount small i)=∑ j,columnLargeCount small j := by
    unfold rowLargeCount columnLargeCount
    exact Finset.sum_comm
  have hrt (i : I) : ((r i-smallRow small (smallView small z false) i:ℕ):ℤ)=
      (r i:ℤ)-(smallRow small (smallView small z false) i:ℤ) := Nat.cast_sub (hr i)
  have hct (j : J) : ((c j-smallColumn small B (smallView small z true) j:ℕ):ℤ)=
      (c j:ℤ)-(smallColumn small B (smallView small z true) j:ℤ) := Nat.cast_sub (hc j)
  apply Int.natCast_inj.mp
  simp only [Nat.cast_sum,Nat.cast_add,Nat.cast_mul]
  simp_rw [hrt,hct]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.sum_mul,←Nat.cast_sum]
  rw [htotal,hs,hlarge]

/-- The executable tests need bounds, a local pattern and the row/column
inequalities, with equality on small incident margins. No completion
enumeration or additional residual-total oracle is necessary. -/
theorem profileFeasible_of_lineTests (r : I → ℕ) (c : J → ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) (z : SmallProfile (paperSmall r c))
    (hb : ∀ a,z a ≤ stateCapacity r c a.1.val.1 a.1.val.2)
    (hp : Pattern (paperSmall r c) (stateCapacity r c) z)
    (hr : ∀ i,smallRow (paperSmall r c) (smallView (paperSmall r c) z false) i≤r i ∧
      (r i<(dimensionAllowance (I := I) (J := J))^20 →
        smallRow (paperSmall r c) (smallView (paperSmall r c) z false) i=r i))
    (hc : ∀ j,smallColumn (paperSmall r c) (stateCapacity r c)
      (smallView (paperSmall r c) z true) j≤c j ∧
      (c j<(dimensionAllowance (I := I) (J := J))^20 →
        smallColumn (paperSmall r c) (stateCapacity r c)
          (smallView (paperSmall r c) z true) j=c j)) :
    ProfileFeasible r c z := by
  refine ⟨hb,hp,⟨fun i => (hr i).1,fun j => (hc j).1⟩,?_,?_,?_⟩
  · intro i hi
    have hi' : r i<(dimensionAllowance (I := I) (J := J))^20 := by omega
    unfold profileRows
    rw [(hr i).2 hi']
    simp [rowLargeCount,paperSmall,firstPaperSmall,hi']
  · intro j hj
    have hj' : c j<(dimensionAllowance (I := I) (J := J))^20 := by omega
    unfold profileColumns
    rw [(hc j).2 hj']
    simp [columnLargeCount,paperSmall,firstPaperSmall,hj']
  · exact padded_residual_totals _ _ z r c _ htotal hp (fun i => (hr i).1) (fun j => (hc j).1)

lemma profileFeasible_lineTests (r : I → ℕ) (c : J → ℕ)
    (z : SmallProfile (paperSmall r c)) (h : ProfileFeasible r c z) :
    (∀ i,smallRow (paperSmall r c) (smallView (paperSmall r c) z false) i≤r i ∧
      (r i<(dimensionAllowance (I := I) (J := J))^20 →
        smallRow (paperSmall r c) (smallView (paperSmall r c) z false) i=r i)) ∧
    (∀ j,smallColumn (paperSmall r c) (stateCapacity r c)
      (smallView (paperSmall r c) z true) j≤c j ∧
      (c j<(dimensionAllowance (I := I) (J := J))^20 →
        smallColumn (paperSmall r c) (stateCapacity r c)
          (smallView (paperSmall r c) z true) j=c j)) := by
  constructor
  · intro i
    refine ⟨h.residuals.1 i,?_⟩
    intro hi
    have hz := h.rows_outside i (by omega)
    unfold profileRows at hz
    have hb := h.residuals.1 i
    omega
  · intro j
    refine ⟨h.residuals.2 j,?_⟩
    intro hj
    have hz := h.columns_outside j (by omega)
    unfold profileColumns at hz
    have hb := h.residuals.2 j
    omega

end
end ContingencyTables.SmallGraphProfiles

end OAI
