import OAI.Combinatorics.ContingencyTables.Transport.NestedPenaltyApplication
import OAI.Combinatorics.ContingencyTables.Model

namespace OAI

/-!
# Literal doubled row and column penalties

The false coordinate of a cell is its row value x. Its true coordinate
is y, with physical column value q=B-y. Thus row and column factor groups
are disjoint, while their small-cell subsets are nested inside them.
Offsets below are the actual full margins and capacity sums of the paper.
-/

namespace ContingencyTables.RowColumnPenalties

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS ProductIntegerSignature NestedProductSignature
open NestedPenaltyApplication BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

def cellLine (u : (I × J) × Bool) : I ⊕ J := if u.2 then .inr u.1.2 else .inl u.1.1

def smallCoordinate (small : I → J → Bool) (u : (I × J) × Bool) : Bool := small u.1.1 u.1.2

def rowView (z : ((I × J) × Bool) → ℕ) (i : I) (j : J) : ℕ := z ((i,j),false)
def columnView (B : I → J → ℕ) (z : ((I × J) × Bool) → ℕ) (i : I) (j : J) : ℕ :=
  B i j-z ((i,j),true)

noncomputable def columnCapacity (B : I → J → ℕ) (j : J) : ℕ := ∑ i, B i j
noncomputable def smallColumnCapacity (small : I → J → Bool) (B : I → J → ℕ) (j : J) : ℕ :=
  ∑ i, if small i j then B i j else 0

noncomputable def fullOffset (B : I → J → ℕ) (rbar : I → ℕ) (cbar : J → ℕ) : I ⊕ J → ℝ :=
  Sum.elim (fun i => -(rbar i:ℝ)) (fun j => (columnCapacity B j:ℝ)-cbar j)

def viewSlope : I ⊕ J → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)

noncomputable def smallOffset (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) : I ⊕ J → ℝ :=
  Sum.elim (fun i => -(r i:ℝ)) (fun j => (smallColumnCapacity small B j:ℝ)-c j)

lemma lineTotal_row (z : ((I × J) × Bool) → ℕ) (i : I) :
    lineTotal cellLine z (.inl i)=∑ j, rowView z i j := by
  simp [lineTotal,cellLine,Fintype.sum_prod_type,rowView]
  rw [Finset.sum_comm]
  simp

lemma lineTotal_column (z : ((I × J) × Bool) → ℕ) (j : J) :
    lineTotal cellLine z (.inr j)=∑ i, z ((i,j),true) := by
  simp [lineTotal,cellLine,Fintype.sum_prod_type]

lemma smallTotal_row (small : I → J → Bool) (z : ((I × J) × Bool) → ℕ) (i : I) :
    smallTotal cellLine (smallCoordinate small) z (.inl i)=
      ∑ j, if small i j then rowView z i j else 0 := by
  simp [smallTotal,lineTotal,cellLine,smallCoordinate,Fintype.sum_prod_type,rowView,
    ite_and]

lemma smallTotal_column (small : I → J → Bool) (z : ((I × J) × Bool) → ℕ) (j : J) :
    smallTotal cellLine (smallCoordinate small) z (.inr j)=
      ∑ i, if small i j then z ((i,j),true) else 0 := by
  simp [smallTotal,lineTotal,cellLine,smallCoordinate,Fintype.sum_prod_type,
    ite_and]

omit [Fintype J] in
lemma columnViews_add (B : I → J → ℕ) (z : ((I × J) × Bool) → ℕ)
    (hz : InBox (fun u => B u.1.1 u.1.2) z) (j : J) :
    (∑ i, columnView B z i j)+(∑ i, z ((i,j),true))=columnCapacity B j := by
  unfold columnView columnCapacity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact Nat.sub_add_cancel (hz ((i,j),true))

omit [Fintype J] in
lemma smallColumnViews_add (small : I → J → Bool) (B : I → J → ℕ)
    (z : ((I × J) × Bool) → ℕ) (hz : InBox (fun u => B u.1.1 u.1.2) z) (j : J) :
    (∑ i, if small i j then columnView B z i j else 0)+
      (∑ i, if small i j then z ((i,j),true) else 0)=smallColumnCapacity small B j := by
  unfold columnView smallColumnCapacity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hs : small i j
  · simp
  · simp only [ite_true]
    exact Nat.sub_add_cancel (hz ((i,j),true))

lemma full_affine_row (B : I → J → ℕ) (rbar : I → ℕ) (cbar : J → ℕ)
    (z : ((I × J) × Bool) → ℕ) (i : I) :
    fullOffset B rbar cbar (.inl i)+(lineTotal cellLine z (.inl i):ℝ)*viewSlope (I := I) (J := J) (.inl i) =
      ((∑ j, rowView z i j):ℝ)-rbar i := by
  rw [lineTotal_row]
  simp [fullOffset,viewSlope]
  ring

lemma full_affine_column (B : I → J → ℕ) (rbar : I → ℕ) (cbar : J → ℕ)
    (z : ((I × J) × Bool) → ℕ) (hz : InBox (fun u => B u.1.1 u.1.2) z) (j : J) :
    fullOffset B rbar cbar (.inr j)+(lineTotal cellLine z (.inr j):ℝ)*viewSlope (I := I) (J := J) (.inr j) =
      ((∑ i, columnView B z i j):ℝ)-cbar j := by
  have h : ((∑ i, columnView B z i j):ℝ)+((∑ i, z ((i,j),true)):ℝ)=columnCapacity B j := by
    exact_mod_cast columnViews_add B z hz j
  rw [lineTotal_column]
  simp only [fullOffset,viewSlope,Sum.elim_inr,mul_neg_one]
  push_cast
  linarith

lemma small_affine_row (small : I → J → Bool) (B : I → J → ℕ) (r : I → ℕ) (c : J → ℕ)
    (z : ((I × J) × Bool) → ℕ) (i : I) :
    smallOffset small B r c (.inl i)+
      (smallTotal cellLine (smallCoordinate small) z (.inl i):ℝ)*viewSlope (I := I) (J := J) (.inl i) =
      ((∑ j, if small i j then rowView z i j else 0):ℝ)-r i := by
  rw [smallTotal_row]
  simp [smallOffset,viewSlope]
  ring

lemma small_affine_column (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (z : ((I × J) × Bool) → ℕ)
    (hz : InBox (fun u => B u.1.1 u.1.2) z) (j : J) :
    smallOffset small B r c (.inr j)+
      (smallTotal cellLine (smallCoordinate small) z (.inr j):ℝ)*viewSlope (I := I) (J := J) (.inr j) =
      ((∑ i, if small i j then columnView B z i j else 0):ℝ)-c j := by
  have h : ((∑ i, if small i j then columnView B z i j else 0):ℝ)+
      ((∑ i, if small i j then z ((i,j),true) else 0):ℝ)=smallColumnCapacity small B j := by
    exact_mod_cast smallColumnViews_add small B z hz j
  rw [smallTotal_column]
  simp only [smallOffset,viewSlope,Sum.elim_inr,mul_neg_one]
  push_cast
  linarith

/-- This is exactly the manuscript's full row/column deviation plus its
small residual violation penalty, on the actual doubled physical box. -/
theorem penalty_eq (small : I → J → Bool) (B : I → J → ℕ)
    (r cR : I → ℕ) (c cC : J → ℕ) (z : ((I × J) × Bool) → ℕ)
    (hz : InBox (fun u => B u.1.1 u.1.2) z) :
    penalty cellLine (smallCoordinate small) (fullOffset B cR cC) viewSlope
      (smallOffset small B r c) viewSlope z =
      (∑ i, |((∑ j, rowView z i j):ℝ)-cR i|)+
      (∑ j, |((∑ i, columnView B z i j):ℝ)-cC j|)+
      (∑ i, max (((∑ j, if small i j then rowView z i j else 0):ℝ)-r i) 0)+
      (∑ j, max (((∑ i, if small i j then columnView B z i j else 0):ℝ)-c j) 0) := by
  unfold penalty
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp_rw [full_affine_row,full_affine_column B cR cC z hz,
    small_affine_row,small_affine_column small B r c z hz]
  ring

def FullConditions (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (z : ((I × J) × Bool) → ℕ) : Prop :=
  (∀ i, ∑ j, rowView z i j=rbar i) ∧
    (∀ j, ∑ i, columnView B z i j=cbar j) ∧
    (∀ i, (∑ j, if small i j then rowView z i j else 0) ≤ r i) ∧
    (∀ j, (∑ i, if small i j then columnView B z i j else 0) ≤ c j)

/-- Zero penalty means precisely the enlarged full margins and
nonnegative original residuals, even for unbalanced defect profiles. -/
theorem penalty_zero_iff (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (z : ((I × J) × Bool) → ℕ)
    (hz : InBox (fun u => B u.1.1 u.1.2) z) :
    penalty cellLine (smallCoordinate small) (fullOffset B rbar cbar) viewSlope
      (smallOffset small B r c) viewSlope z=0 ↔ FullConditions small B r rbar c cbar z := by
  rw [penalty_eq small B r rbar c cbar z hz]
  let a : I → ℝ := fun i => |((∑ j, rowView z i j):ℝ)-rbar i|
  let b : J → ℝ := fun j => |((∑ i, columnView B z i j):ℝ)-cbar j|
  let e : I → ℝ := fun i => max (((∑ j, if small i j then rowView z i j else 0):ℝ)-r i) 0
  let f : J → ℝ := fun j => max (((∑ i, if small i j then columnView B z i j else 0):ℝ)-c j) 0
  have ha : ∀ i, 0 ≤ a i := fun _ => abs_nonneg _
  have hb : ∀ j, 0 ≤ b j := fun _ => abs_nonneg _
  have he : ∀ i, 0 ≤ e i := fun _ => le_max_right _ _
  have hf : ∀ j, 0 ≤ f j := fun _ => le_max_right _ _
  change (∑ i, a i)+(∑ j, b j)+(∑ i, e i)+(∑ j, f j)=0 ↔ _
  constructor
  · intro hzero
    have hsa : 0 ≤ ∑ i, a i := Finset.sum_nonneg (fun i _ => ha i)
    have hsb : 0 ≤ ∑ j, b j := Finset.sum_nonneg (fun j _ => hb j)
    have hse : 0 ≤ ∑ i, e i := Finset.sum_nonneg (fun i _ => he i)
    have hsf : 0 ≤ ∑ j, f j := Finset.sum_nonneg (fun j _ => hf j)
    refine ⟨?_,?_,?_,?_⟩
    · intro i
      have hi := Finset.single_le_sum (fun k _ => ha k) (Finset.mem_univ i)
      have hzabs : a i=0 := by linarith [ha i]
      have hiReal := sub_eq_zero.mp (abs_eq_zero.mp hzabs)
      exact_mod_cast hiReal
    · intro j
      have hj := Finset.single_le_sum (fun k _ => hb k) (Finset.mem_univ j)
      have hzabs : b j=0 := by linarith [hb j]
      have hjReal := sub_eq_zero.mp (abs_eq_zero.mp hzabs)
      exact_mod_cast hjReal
    · intro i
      have hi := Finset.single_le_sum (fun k _ => he k) (Finset.mem_univ i)
      have ht : (((∑ j, if small i j then rowView z i j else 0):ℝ)-r i) ≤ 0 := by
        have hm := le_max_left (((∑ j, if small i j then rowView z i j else 0):ℝ)-r i) 0
        change _ ≤ e i at hm
        linarith
      exact_mod_cast (sub_nonpos.mp ht)
    · intro j
      have hj := Finset.single_le_sum (fun k _ => hf k) (Finset.mem_univ j)
      have ht : (((∑ i, if small i j then columnView B z i j else 0):ℝ)-c j) ≤ 0 := by
        have hm := le_max_left (((∑ i, if small i j then columnView B z i j else 0):ℝ)-c j) 0
        change _ ≤ f j at hm
        linarith
      exact_mod_cast (sub_nonpos.mp ht)
  · rintro ⟨hr,hc,hsr,hsc⟩
    have haz : ∀ i, a i=0 := by
      intro i
      have hh : ((∑ j, rowView z i j):ℝ)=rbar i := by exact_mod_cast hr i
      exact abs_eq_zero.mpr (sub_eq_zero.mpr hh)
    have hbz : ∀ j, b j=0 := by
      intro j
      have hh : ((∑ i, columnView B z i j):ℝ)=cbar j := by exact_mod_cast hc j
      exact abs_eq_zero.mpr (sub_eq_zero.mpr hh)
    have hez : ∀ i, e i=0 := by
      intro i
      apply max_eq_right
      exact sub_nonpos.mpr (by exact_mod_cast hsr i)
    have hfz : ∀ j, f j=0 := by
      intro j
      apply max_eq_right
      exact sub_nonpos.mpr (by exact_mod_cast hsc j)
    simp only [haz,hbz,hez,hfz,Finset.sum_const_zero,add_zero]

end ContingencyTables.RowColumnPenalties

end OAI
