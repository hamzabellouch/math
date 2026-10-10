import OAI.Combinatorics.ContingencyTables.Transport.FiniteExchangeObservables
import OAI.Combinatorics.ContingencyTables.Transport.RectangleCompletions
import OAI.Combinatorics.ContingencyTables.Sampling.SmallContextCoordinates

namespace OAI

/-! # Selected doubled-coordinate sums are the physical small margins -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates PhysicalCompletionFibres FirstPaperProfiles PaddedCompletions
open IntegerWeightedTransport CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def selectedRow (small : I → J → Bool) (z : SmallProfile small) (b : Bool) (i : I) : ℕ :=
  ∑ a,if a.1.val.1=i ∧ a.2=b then z a else 0

noncomputable def selectedColumn (small : I → J → Bool) (z : SmallProfile small) (b : Bool) (j : J) : ℕ :=
  ∑ a,if a.1.val.2=j ∧ a.2=b then z a else 0

omit [LinearOrder I] [LinearOrder J] in
lemma selected_bool_sum (small : I → J → Bool) (z : SmallProfile small) (b : Bool)
    (p : Cells small → Prop) :
    (∑ a : Cells small×Bool,if p a.1 ∧ a.2=b then z a else 0)=
      ∑ a : Cells small,if p a then z (a,b) else 0 := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  cases b <;> simp

omit [LinearOrder I] [LinearOrder J] in
lemma cell_sum_as_matrix (small : I → J → Bool) (z : SmallProfile small) (b : Bool)
    (p : I×J → Prop) :
    (∑ a : Cells small,if p a.val then z (a,b) else 0)=
      ∑ a : I×J,if p a then smallView small z b a.1 a.2 else 0 := by
  have hzero (a : I×J) (ha : ¬small a.1 a.2=true) :
      (if p a then smallView small z b a.1 a.2 else 0)=0 := by
    by_cases hp : p a
    · simp only [hp,ite_true,smallView,dite_eq_right ha]
    · rw [ite_eq_right hp]
  have he := sum_subtype_eq_of_zero (fun a : I×J => small a.1 a.2=true)
    (fun a => if p a then smallView small z b a.1 a.2 else 0) hzero
  calc
    _ = ∑ a : Cells small,if p a.val then smallView small z b a.val.1 a.val.2 else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [smallView,a.property,dite_eq_left]
    _ = _ := by
      convert he using 1
      congr 2
      exact Subsingleton.elim _ _

omit [LinearOrder J] in
lemma selectedRow_eq (small : I → J → Bool) (z : SmallProfile small) (b : Bool) (i : I) :
    selectedRow small z b i=∑ j,smallView small z b i j := by
  unfold selectedRow
  have hb : (∑ a,if a.1.val.1=i ∧ a.2=b then z a else 0)=
      ∑ a : Cells small,if a.val.1=i then z (a,b) else 0 := by
    convert selected_bool_sum small z b (fun a => a.val.1=i) using 1
    all_goals
      congr 4
      first | exact Subsingleton.elim _ _ | (funext a; split_ifs <;> rfl)
  rw [hb]
  have hc : (∑ a : Cells small,if a.val.1=i then z (a,b) else 0)=
      ∑ a : I×J,if a.1=i then smallView small z b a.1 a.2 else 0 := by
    convert cell_sum_as_matrix small z b (fun a => a.1=i) using 1
    all_goals
      congr 4
      first | exact Subsingleton.elim _ _ | (funext a; split_ifs <;> rfl)
  rw [hc,Fintype.sum_prod_type]
  simp_rw [Finset.sum_ite_irrel]
  simp

omit [LinearOrder I] in
lemma selectedColumn_eq (small : I → J → Bool) (z : SmallProfile small) (b : Bool) (j : J) :
    selectedColumn small z b j=∑ i,smallView small z b i j := by
  unfold selectedColumn
  have hb : (∑ a,if a.1.val.2=j ∧ a.2=b then z a else 0)=
      ∑ a : Cells small,if a.val.2=j then z (a,b) else 0 := by
    convert selected_bool_sum small z b (fun a => a.val.2=j) using 1
    all_goals
      congr 4
      first | exact Subsingleton.elim _ _ | (funext a; split_ifs <;> rfl)
  rw [hb]
  have hc : (∑ a : Cells small,if a.val.2=j then z (a,b) else 0)=
      ∑ a : I×J,if a.2=j then smallView small z b a.1 a.2 else 0 := by
    convert cell_sum_as_matrix small z b (fun a => a.2=j) using 1
    all_goals
      congr 4
      first | exact Subsingleton.elim _ _ | (funext a; split_ifs <;> rfl)
  rw [hc,Fintype.sum_prod_type,Finset.sum_comm]
  simp_rw [Finset.sum_ite_irrel]
  simp

omit [LinearOrder J] in
lemma selectedRow_eq_smallRow (small : I → J → Bool) (z : SmallProfile small) (i : I) :
    selectedRow small z false i=smallRow small (smallView small z false) i := by
  rw [selectedRow_eq]
  unfold smallRow
  apply Finset.sum_congr rfl
  intro j _
  cases hs : small i j <;> simp [smallView,hs]

omit [LinearOrder I] in
lemma smallColumn_cast_selected (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (hz : ∀ a,z a ≤ B a.1.val.1 a.1.val.2) (j : J) :
    (smallColumn small B (smallView small z true) j:ℤ)=
      (∑ i,if small i j then (B i j:ℤ) else 0)-(selectedColumn small z true j:ℤ) := by
  rw [selectedColumn_eq]
  unfold smallColumn
  rw [Nat.cast_sum,Nat.cast_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hs : small i j=true
  · have hb := hz (⟨(i,j),hs⟩,true)
    simp only [hs,ite_true,smallView,dite_eq_left]
    exact Nat.cast_sub hb
  · simp only [smallView,dite_eq_right hs,ite_eq_right hs,Nat.cast_zero,sub_zero]

lemma exchange_smallRow_abs (small : I → J → Bool) (X Y : SmallProfile small)
    (hxy : IntegerExchangeAdjacent X Y) (i : I) :
    |(smallRow small (smallView small Y false) i:ℤ)-smallRow small (smallView small X false) i| ≤ 2 := by
  rw [← selectedRow_eq_smallRow,← selectedRow_eq_smallRow]
  unfold selectedRow
  convert exchange_selected_sum_abs_le_two (fun a => a.1.val.1=i ∧ a.2=false) X Y hxy using 1
  congr 5 <;> first | exact Subsingleton.elim _ _ | (funext a; split_ifs <;> rfl)

lemma exchange_smallColumn_abs (small : I → J → Bool) (B : I → J → ℕ)
    (X Y : SmallProfile small) (hX : ∀ a,X a ≤ B a.1.val.1 a.1.val.2)
    (hY : ∀ a,Y a ≤ B a.1.val.1 a.1.val.2)
    (hxy : IntegerExchangeAdjacent X Y) (j : J) :
    |(smallColumn small B (smallView small Y true) j:ℤ)-smallColumn small B (smallView small X true) j| ≤ 2 := by
  rw [smallColumn_cast_selected small B Y hY,smallColumn_cast_selected small B X hX]
  have he : (∑ i,if small i j then (B i j:ℤ) else 0)-(selectedColumn small Y true j:ℤ)-
      ((∑ i,if small i j then (B i j:ℤ) else 0)-(selectedColumn small X true j:ℤ))=
      -((selectedColumn small Y true j:ℤ)-selectedColumn small X true j) := by ring
  rw [he,abs_neg]
  unfold selectedColumn
  convert exchange_selected_sum_abs_le_two (fun a => a.1.val.2=j ∧ a.2=true) X Y hxy using 1
  congr 5 <;> first | exact Subsingleton.elim _ _ | (funext a; split_ifs <;> rfl)

end ContingencyTables.SmallGraphProfiles

end OAI
