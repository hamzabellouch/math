import Mathlib
import OAI.Probability.CoordinateSweeps.Grid
import OAI.RepresentationTheory.Unitary.Basic
import OAI.Analysis.Matrix.TensorMoment

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.Grid

/- Concatenation of the *ordered* coordinate sequences. -/
def concat (A B : Grid) : Grid where
  b := A.b+B.b
  positive := Nat.add_pos_left A.positive _
  bits := Fin.addCases A.bits B.bits

@[simp] lemma concat_bits_left (A B : Grid) (i : Fin A.b) :
    (concat A B).bits (Fin.castAdd B.b i)=A.bits i := by simp [concat]
@[simp] lemma concat_bits_right (A B : Grid) (i : Fin B.b) :
    (concat A B).bits (Fin.natAdd A.b i)=B.bits i := by simp [concat]

/- Literal Cartesian identification for the split, retaining all bit labels. -/
def splitSlots (A B : Grid) : (concat A B).Slot ≃ A.Slot × B.Slot :=
  ((Equiv.prodPiEquivSumPi (fun i => Cube (A.bits i)) (fun j => Cube (B.bits j))).trans
    (Equiv.piCongr finSumFinEquiv (fun i => by
      cases i with
      | inl i => exact Equiv.cast (by simp [concat])
      | inr j => exact Equiv.cast (by simp [concat])))).symm

@[simp] lemma splitSlots_left (A B : Grid) (x : (concat A B).Slot) (i : Fin A.b) :
    (splitSlots A B x).1 i = (Equiv.cast (by simp : Cube ((concat A B).bits (Fin.castAdd B.b i))=Cube (A.bits i)))
      (x (Fin.castAdd B.b i)) := by
  rfl

@[simp] lemma splitSlots_right (A B : Grid) (x : (concat A B).Slot) (j : Fin B.b) :
    (splitSlots A B x).2 j = (Equiv.cast (by simp : Cube ((concat A B).bits (Fin.natAdd A.b j))=Cube (B.bits j)))
      (x (Fin.natAdd A.b j)) := by
  rfl

lemma concat_size (A B : Grid) : (concat A B).size=A.size*B.size := by
  change (∏ j : Fin (A.b+B.b), 2^Fin.addCases A.bits B.bits j)=A.size*B.size
  rw [Fin.prod_univ_add]
  simp [size]

lemma concat_allowed (A B : Grid) (r : ℕ) :
    (concat A B).Allowed r ↔ A.Allowed r ∧ B.Allowed r := by
  constructor
  · intro h
    exact ⟨fun i => by simpa using h (Fin.castAdd B.b i),
      fun i => by simpa using h (Fin.natAdd A.b i)⟩
  · rintro ⟨hA,hB⟩ i
    induction i using Fin.addCases with
    | left i => simpa using hA i
    | right i => simpa using hB i

end CoordinateSweeps.Grid

noncomputable section
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps

/- Deleting a head coordinate commutes with the literal Fin concatenation. -/
def finDeleteLeft {m n : ℕ} (i : Fin m) :
    ({j : Fin m // j ≠ i} ⊕ Fin n) ≃ {j : Fin (m+n) // j ≠ Fin.castAdd n i} where
  toFun z := match z with
    | Sum.inl j => ⟨Fin.castAdd n j.val,by simpa using j.property⟩
    | Sum.inr j => ⟨Fin.natAdd m j,by intro h; have ht := congrArg Fin.val h; simp at ht; omega⟩
  invFun z := Fin.addCases (motive := fun j : Fin (m+n) => j ≠ Fin.castAdd n i → ({j : Fin m // j ≠ i} ⊕ Fin n))
    (fun j (h : Fin.castAdd n j ≠ Fin.castAdd n i) => Sum.inl ⟨j,by simpa using h⟩)
    (fun j (_h : Fin.natAdd m j ≠ Fin.castAdd n i) => Sum.inr j) z.val z.property
  left_inv z := by cases z <;> simp
  right_inv z := by
    rcases z with ⟨j,hj⟩
    induction j using Fin.addCases with
    | left j => simp
    | right j => simp

@[simp] lemma finDeleteLeft_inl {m n : ℕ} (i : Fin m) (j : {j : Fin m // j ≠ i}) :
    (finDeleteLeft (n := n) i (Sum.inl j)).val=Fin.castAdd n j.val := rfl
@[simp] lemma finDeleteLeft_inr {m n : ℕ} (i : Fin m) (j : Fin n) :
    (finDeleteLeft (n := n) i (Sum.inr j)).val=Fin.natAdd m j := rfl

/- Deleting a tail coordinate, in the same original head-then-tail order. -/
def finDeleteRight {m n : ℕ} (i : Fin n) :
    (Fin m ⊕ {j : Fin n // j ≠ i}) ≃ {j : Fin (m+n) // j ≠ Fin.natAdd m i} where
  toFun z := match z with
    | Sum.inl j => ⟨Fin.castAdd n j,by intro h; have ht := congrArg Fin.val h; simp at ht; omega⟩
    | Sum.inr j => ⟨Fin.natAdd m j.val,by simpa using j.property⟩
  invFun z := Fin.addCases (motive := fun j : Fin (m+n) => j ≠ Fin.natAdd m i → (Fin m ⊕ {j : Fin n // j ≠ i}))
    (fun j (_h : Fin.castAdd n j ≠ Fin.natAdd m i) => Sum.inl j)
    (fun j (h : Fin.natAdd m j ≠ Fin.natAdd m i) => Sum.inr ⟨j,by simpa using h⟩) z.val z.property
  left_inv z := by cases z <;> simp
  right_inv z := by
    rcases z with ⟨j,hj⟩
    induction j using Fin.addCases with
    | left j => simp
    | right j => simp

@[simp] lemma finDeleteRight_inl {m n : ℕ} (i : Fin n) (j : Fin m) :
    (finDeleteRight (m := m) i (Sum.inl j)).val=Fin.castAdd n j := rfl
@[simp] lemma finDeleteRight_inr {m n : ℕ} (i : Fin n) (j : {j : Fin n // j ≠ i}) :
    (finDeleteRight (m := m) i (Sum.inr j)).val=Fin.natAdd m j.val := rfl

end CoordinateSweeps

namespace CoordinateSweeps.Grid

/- Row line chart: the other head coordinates and the fixed tail row label. -/
def rowLines (A B : Grid) (i : Fin A.b) :
    (A.Line i × B.Slot) ≃ (concat A B).Line (Fin.castAdd B.b i) :=
  (Equiv.prodPiEquivSumPi (fun j : {j : Fin A.b // j ≠ i} => Cube (A.bits j))
    (fun k => Cube (B.bits k))).trans
    (Equiv.piCongr (finDeleteLeft (n := B.b) i) (fun j => by
      cases j with
      | inl j => exact Equiv.cast (by
          change Cube (A.bits j)=Cube (Fin.addCases A.bits B.bits (Fin.castAdd B.b j))
          simp)
      | inr k => exact Equiv.cast (by
          change Cube (B.bits k)=Cube (Fin.addCases A.bits B.bits (Fin.natAdd A.b k))
          simp)))

/- Column line chart: the fixed head label and the other tail coordinates. -/
def columnLines (A B : Grid) (i : Fin B.b) :
    (A.Slot × B.Line i) ≃ (concat A B).Line (Fin.natAdd A.b i) :=
  (Equiv.prodPiEquivSumPi (fun j => Cube (A.bits j))
    (fun k : {k : Fin B.b // k ≠ i} => Cube (B.bits k))).trans
    (Equiv.piCongr (finDeleteRight (m := A.b) i) (fun j => by
      cases j with
      | inl j => exact Equiv.cast (by
          change Cube (A.bits j)=Cube (Fin.addCases A.bits B.bits (Fin.castAdd B.b j))
          simp)
      | inr k => exact Equiv.cast (by
          change Cube (B.bits k)=Cube (Fin.addCases A.bits B.bits (Fin.natAdd A.b k))
          simp)))

lemma rowLines_evaluation (A B : Grid) (i : Fin A.b) (x : (concat A B).Slot) :
    (rowLines A B i).symm (fun j => x j.val)=
      ((fun j : {j : Fin A.b // j ≠ i} => (splitSlots A B x).1 j.val),(splitSlots A B x).2) := by
  apply Prod.ext
  · funext j
    rfl
  · funext j
    rfl

lemma columnLines_evaluation (A B : Grid) (i : Fin B.b) (x : (concat A B).Slot) :
    (columnLines A B i).symm (fun j => x j.val)=
      ((splitSlots A B x).1,(fun j : {j : Fin B.b // j ≠ i} => (splitSlots A B x).2 j.val)) := by
  apply Prod.ext
  · funext j
    rfl
  · funext j
    rfl

end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid

def leftCube (A B : Grid) (i : Fin A.b) :
    Cube ((concat A B).bits (Fin.castAdd B.b i)) ≃ Cube (A.bits i) :=
  Equiv.cast (by simp)
def rightCube (A B : Grid) (j : Fin B.b) :
    Cube ((concat A B).bits (Fin.natAdd A.b j)) ≃ Cube (B.bits j) :=
  Equiv.cast (by simp)

def prefixFiber (A B : Grid) (i : Fin A.b) :
    ((concat A B).Line (Fin.castAdd B.b i) → Equiv.Perm (Cube ((concat A B).bits (Fin.castAdd B.b i)))) ≃
      (B.Slot → A.Line i → Equiv.Perm (Cube (A.bits i))) :=
  (Equiv.arrowCongr ((rowLines A B i).symm.trans (Equiv.prodComm _ _))
    (leftCube A B i).permCongr).trans (Equiv.curry _ _ _)

def suffixFiber (A B : Grid) (i : Fin B.b) :
    ((concat A B).Line (Fin.natAdd A.b i) → Equiv.Perm (Cube ((concat A B).bits (Fin.natAdd A.b i)))) ≃
      (A.Slot → B.Line i → Equiv.Perm (Cube (B.bits i))) :=
  (Equiv.arrowCongr (columnLines A B i).symm
    (rightCube A B i).permCongr).trans (Equiv.curry _ _ _)

/- Exact two-part choice-space equivalence, not just an equality in law. -/
def choicesSplit (A B : Grid) : (concat A B).Choices ≃
    ((B.Slot → A.Choices) × (A.Slot → B.Choices)) :=
  ((Equiv.prodCongr
    (Equiv.piComm (fun (_y : B.Slot) (i : Fin A.b) => A.Line i → Equiv.Perm (Cube (A.bits i))))
    (Equiv.piComm (fun (_x : A.Slot) (i : Fin B.b) => B.Line i → Equiv.Perm (Cube (B.bits i))))).trans
    ((Equiv.prodPiEquivSumPi
      (fun i : Fin A.b => B.Slot → A.Line i → Equiv.Perm (Cube (A.bits i)))
      (fun i : Fin B.b => A.Slot → B.Line i → Equiv.Perm (Cube (B.bits i)))).trans
      (Equiv.piCongr finSumFinEquiv (fun i => by
        cases i with
        | inl i => exact (prefixFiber A B i).symm
        | inr j => exact (suffixFiber A B j).symm)))).symm

def rowChoices (A B : Grid) (ω : (concat A B).Choices) (y : B.Slot) : A.Choices :=
  (choicesSplit A B ω).1 y
def columnChoices (A B : Grid) (ω : (concat A B).Choices) (x : A.Slot) : B.Choices :=
  (choicesSplit A B ω).2 x

lemma rowChoices_apply (A B : Grid) (ω : (concat A B).Choices) (y : B.Slot)
    (i : Fin A.b) (L : A.Line i) :
    rowChoices A B ω y i L=(leftCube A B i).permCongr
      (ω (Fin.castAdd B.b i) (rowLines A B i (L,y))) := by rfl

lemma columnChoices_apply (A B : Grid) (ω : (concat A B).Choices) (x : A.Slot)
    (i : Fin B.b) (L : B.Line i) :
    columnChoices A B ω x i L=(rightCube A B i).permCongr
      (ω (Fin.natAdd A.b i) (columnLines A B i (x,L))) := by rfl

end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid

lemma rowLines_at_slot (A B : Grid) (i : Fin A.b) (x : (concat A B).Slot) :
    rowLines A B i ((fun j => (splitSlots A B x).1 j.val),(splitSlots A B x).2)=
      (fun (j : {j : Fin (concat A B).b // j ≠ Fin.castAdd B.b i}) => x j.val) := by
  have hh := congrArg (rowLines A B i) (rowLines_evaluation A B i x)
  simpa using hh.symm

lemma columnLines_at_slot (A B : Grid) (i : Fin B.b) (x : (concat A B).Slot) :
    columnLines A B i ((splitSlots A B x).1,(fun j => (splitSlots A B x).2 j.val))=
      (fun (j : {j : Fin (concat A B).b // j ≠ Fin.natAdd A.b i}) => x j.val) := by
  have hh := congrArg (columnLines A B i) (columnLines_evaluation A B i x)
  simpa using hh.symm

/- A head stage really acts by independent row stages in the Cartesian chart. -/
theorem stage_split_left (A B : Grid) (ω : (concat A B).Choices) (i : Fin A.b)
    (x : (concat A B).Slot) :
    splitSlots A B ((concat A B).stage ω (Fin.castAdd B.b i) x)=
      (A.stage (rowChoices A B ω (splitSlots A B x).2) i (splitSlots A B x).1,
        (splitSlots A B x).2) := by
  apply Prod.ext
  · funext j
    by_cases h : j=i
    · subst j
      change leftCube A B i ((concat A B).stage ω (Fin.castAdd B.b i) x (Fin.castAdd B.b i))=A.stage (rowChoices A B ω (splitSlots A B x).2) i (splitSlots A B x).1 i
      erw [stage_apply_same,stage_apply_same,rowChoices_apply]
      simp only [Equiv.permCongr_apply,rowLines_at_slot]
      change leftCube A B i (ω _ _ (x _))=leftCube A B i (ω _ _ ((leftCube A B i).symm (leftCube A B i (x _))))
      rw [Equiv.symm_apply_apply]
    · change leftCube A B j ((concat A B).stage ω (Fin.castAdd B.b i) x (Fin.castAdd B.b j))=A.stage (rowChoices A B ω (splitSlots A B x).2) i (splitSlots A B x).1 j
      erw [stage_apply_ne _ _ _ _ h]
      change leftCube A B j ((concat A B).stage ω (Fin.castAdd B.b i) x (Fin.castAdd B.b j))=leftCube A B j (x _)
      erw [stage_apply_ne _ _ _ _ (by intro hh; apply h; apply Fin.ext; have := congrArg Fin.val hh; simp at this; omega)]
  · funext j
    change rightCube A B j ((concat A B).stage ω (Fin.castAdd B.b i) x (Fin.natAdd A.b j))=rightCube A B j (x _)
    erw [stage_apply_ne _ _ _ _ (by intro h; have hh := congrArg Fin.val h; simp at hh; omega)]

/- A tail stage really acts by independent column stages. -/
theorem stage_split_right (A B : Grid) (ω : (concat A B).Choices) (i : Fin B.b)
    (x : (concat A B).Slot) :
    splitSlots A B ((concat A B).stage ω (Fin.natAdd A.b i) x)=
      ((splitSlots A B x).1,B.stage (columnChoices A B ω (splitSlots A B x).1) i (splitSlots A B x).2) := by
  apply Prod.ext
  · funext j
    change leftCube A B j ((concat A B).stage ω (Fin.natAdd A.b i) x (Fin.castAdd B.b j))=leftCube A B j (x _)
    erw [stage_apply_ne _ _ _ _ (by intro h; have hh := congrArg Fin.val h; simp at hh; omega)]
  · funext j
    by_cases h : j=i
    · subst j
      change rightCube A B i ((concat A B).stage ω (Fin.natAdd A.b i) x (Fin.natAdd A.b i))=B.stage (columnChoices A B ω (splitSlots A B x).1) i (splitSlots A B x).2 i
      erw [stage_apply_same,stage_apply_same,columnChoices_apply]
      simp only [Equiv.permCongr_apply,columnLines_at_slot]
      change rightCube A B i (ω _ _ (x _))=rightCube A B i (ω _ _ ((rightCube A B i).symm (rightCube A B i (x _))))
      rw [Equiv.symm_apply_apply]
    · change rightCube A B j ((concat A B).stage ω (Fin.natAdd A.b i) x (Fin.natAdd A.b j))=B.stage (columnChoices A B ω (splitSlots A B x).1) i (splitSlots A B x).2 j
      erw [stage_apply_ne _ _ _ _ h]
      change rightCube A B j ((concat A B).stage ω (Fin.natAdd A.b i) x (Fin.natAdd A.b j))=rightCube A B j (x _)
      erw [stage_apply_ne _ _ _ _ (by intro hh; apply h; apply Fin.ext; have := congrArg Fin.val hh; simp at this; omega)]

end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid

lemma boundary_split_prefix (A B : Grid) (ω : (concat A B).Choices)
    (x : (concat A B).Slot) (t : ℕ) (ht : t≤A.b) :
    splitSlots A B ((concat A B).boundary ω t x)=
      (A.boundary (rowChoices A B ω (splitSlots A B x).2) t (splitSlots A B x).1,
       (splitSlots A B x).2) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have ha : t<A.b := by omega
    have hc : t<(concat A B).b := by change t<A.b+B.b; omega
    have hi : (⟨t,hc⟩ : Fin (concat A B).b)=Fin.castAdd B.b (⟨t,ha⟩ : Fin A.b) := rfl
    rw [(concat A B).boundary_succ ω hc,A.boundary_succ _ ha]
    simp only [Equiv.Perm.mul_apply]
    rw [hi,stage_split_left,ih (by omega)]

lemma boundary_split_suffix (A B : Grid) (ω : (concat A B).Choices)
    (x : (concat A B).Slot) (t : ℕ) (ht : t≤B.b) :
    splitSlots A B ((concat A B).boundary ω (A.b+t) x)=
      (A.sweep (rowChoices A B ω (splitSlots A B x).2) (splitSlots A B x).1,
       B.boundary (columnChoices A B ω
         (A.sweep (rowChoices A B ω (splitSlots A B x).2) (splitSlots A B x).1)) t
         (splitSlots A B x).2) := by
  induction t with
  | zero => simpa [sweep] using boundary_split_prefix A B ω x A.b le_rfl
  | succ t ih =>
    have hb : t<B.b := by omega
    have hc : A.b+t<(concat A B).b := by change A.b+t<A.b+B.b; omega
    have hi : (⟨A.b+t,hc⟩ : Fin (concat A B).b)=Fin.natAdd A.b (⟨t,hb⟩ : Fin B.b) := rfl
    rw [Nat.add_succ,(concat A B).boundary_succ ω hc,B.boundary_succ _ hb]
    simp only [Equiv.Perm.mul_apply]
    rw [hi,stage_split_right,ih (by omega)]

/- Actual ordered permutation factorization: row sweeps, then column sweeps. -/
theorem sweep_split (A B : Grid) (ω : (concat A B).Choices) (x : (concat A B).Slot) :
    splitSlots A B ((concat A B).sweep ω x)=
      (A.sweep (rowChoices A B ω (splitSlots A B x).2) (splitSlots A B x).1,
       B.sweep (columnChoices A B ω
         (A.sweep (rowChoices A B ω (splitSlots A B x).2) (splitSlots A B x).1))
         (splitSlots A B x).2) :=
  boundary_split_suffix A B ω x B.b le_rfl

end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid

def prefixTime (A B : Grid) (t : Fin (A.b+1)) : Fin ((concat A B).b+1) :=
  ⟨t.val,by change t.val<A.b+B.b+1; have := t.isLt; omega⟩
def suffixTime (A B : Grid) (t : Fin (B.b+1)) : Fin ((concat A B).b+1) :=
  ⟨A.b+t.val,by change A.b+t.val<A.b+B.b+1; have := t.isLt; omega⟩

namespace Holes
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

def rowOf (i : Fin h) : B.Slot := (splitSlots A B (H.path i 0)).2
def columnOf (i : Fin h) : A.Slot := (splitSlots A B (H.path i (suffixTime A B 0))).1

lemma row_constant (i : Fin h) (t : Fin (A.b+1)) :
    (splitSlots A B (H.path i (prefixTime A B t))).2=H.rowOf i := by
  obtain ⟨ω,hω⟩ := H.feasible_of_disjoint
  rw [← hω i (prefixTime A B t)]
  change (splitSlots A B ((concat A B).boundary ω t.val (H.path i 0))).2=_
  rw [boundary_split_prefix A B ω _ t.val (by have := t.isLt; omega)]
  rfl

lemma column_constant (i : Fin h) (t : Fin (B.b+1)) :
    (splitSlots A B (H.path i (suffixTime A B t))).1=H.columnOf i := by
  obtain ⟨ω,hω⟩ := H.feasible_of_disjoint
  unfold columnOf
  rw [← hω i (suffixTime A B t),← hω i (suffixTime A B 0)]
  change (splitSlots A B ((concat A B).boundary ω (A.b+t.val) (H.path i 0))).1=
    (splitSlots A B ((concat A B).boundary ω (A.b+0) (H.path i 0))).1
  rw [boundary_split_suffix A B ω _ t.val (by have := t.isLt; omega),
      boundary_split_suffix A B ω _ 0 (Nat.zero_le _)]

abbrev RowCard (y : B.Slot) := {i : Fin h // H.rowOf i=y}
abbrev ColumnCard (x : A.Slot) := {i : Fin h // H.columnOf i=x}
def rowCount (y : B.Slot) : ℕ := Fintype.card (H.RowCard y)
def columnCount (x : A.Slot) : ℕ := Fintype.card (H.ColumnCard x)
def rowCards (y : B.Slot) : Fin (H.rowCount y) ≃ H.RowCard y := (Fintype.equivFin _).symm
def columnCards (x : A.Slot) : Fin (H.columnCount x) ≃ H.ColumnCard x := (Fintype.equivFin _).symm

/- All holes in one actual row, with the inherited ordered trajectories. -/
def rowHoles (y : B.Slot) : A.Holes (H.rowCount y) where
  path i t := (splitSlots A B (H.path (H.rowCards y i).val (prefixTime A B t))).1
  disjoint t := by
    intro i j hij
    apply (H.rowCards y).injective
    apply Subtype.ext
    apply H.disjoint (prefixTime A B t)
    apply (splitSlots A B).injective
    apply Prod.ext hij
    exact (H.row_constant _ t).trans ((H.rowCards y i).property.trans
      ((H.rowCards y j).property.symm.trans (H.row_constant _ t).symm))
  coordinate_step i j k hk := by
    change leftCube A B k (H.path (H.rowCards y i).val (Fin.castAdd B.b j).succ (Fin.castAdd B.b k))=
      leftCube A B k (H.path (H.rowCards y i).val (Fin.castAdd B.b j).castSucc (Fin.castAdd B.b k))
    apply congrArg
    apply H.coordinate_step
    intro hh
    apply hk
    apply Fin.ext
    exact congrArg (fun u : Fin (A.b+B.b) => u.val) hh

/- All holes in one junction column, with the inherited tail trajectories. -/
def columnHoles (x : A.Slot) : B.Holes (H.columnCount x) where
  path i t := (splitSlots A B (H.path (H.columnCards x i).val (suffixTime A B t))).2
  disjoint t := by
    intro i j hij
    apply (H.columnCards x).injective
    apply Subtype.ext
    apply H.disjoint (suffixTime A B t)
    apply (splitSlots A B).injective
    apply Prod.ext _ hij
    exact (H.column_constant _ t).trans ((H.columnCards x i).property.trans
      ((H.columnCards x j).property.symm.trans (H.column_constant _ t).symm))
  coordinate_step i j k hk := by
    change rightCube A B k (H.path (H.columnCards x i).val (Fin.natAdd A.b j).succ (Fin.natAdd A.b k))=
      rightCube A B k (H.path (H.columnCards x i).val (Fin.natAdd A.b j).castSucc (Fin.natAdd A.b k))
    apply congrArg
    apply H.coordinate_step
    intro hh
    apply hk
    apply Fin.ext
    have := congrArg Fin.val hh
    simp at this
    omega

lemma sum_rowCount : ∑ y, H.rowCount y=h := by
  unfold rowCount
  rw [← Fintype.card_sigma]
  exact (Fintype.card_congr (Equiv.sigmaFiberEquiv H.rowOf)).trans (Fintype.card_fin h)
lemma sum_columnCount : ∑ x, H.columnCount x=h := by
  unfold columnCount
  rw [← Fintype.card_sigma]
  exact (Fintype.card_congr (Equiv.sigmaFiberEquiv H.columnOf)).trans (Fintype.card_fin h)

end Holes
end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid.Holes
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

lemma row_step_iff (y : B.Slot) (τ : A.Choices) :
    (H.rowHoles y).StepCompatible τ ↔ ∀ i : Fin h, H.rowOf i=y → ∀ j : Fin A.b,
      A.stage τ j (splitSlots A B (H.path i (prefixTime A B j.castSucc))).1=
        (splitSlots A B (H.path i (prefixTime A B j.succ))).1 := by
  constructor
  · intro hs i hi j
    obtain ⟨k,hk⟩ := (H.rowCards y).surjective ⟨i,hi⟩
    have he := hs k j
    change A.stage τ j (splitSlots A B (H.path (H.rowCards y k).val (prefixTime A B j.castSucc))).1=
      (splitSlots A B (H.path (H.rowCards y k).val (prefixTime A B j.succ))).1 at he
    simpa only [hk] using he
  · intro hs k j
    exact hs (H.rowCards y k).val (H.rowCards y k).property j

lemma column_step_iff (x : A.Slot) (τ : B.Choices) :
    (H.columnHoles x).StepCompatible τ ↔ ∀ i : Fin h, H.columnOf i=x → ∀ j : Fin B.b,
      B.stage τ j (splitSlots A B (H.path i (suffixTime A B j.castSucc))).2=
        (splitSlots A B (H.path i (suffixTime A B j.succ))).2 := by
  constructor
  · intro hs i hi j
    obtain ⟨k,hk⟩ := (H.columnCards x).surjective ⟨i,hi⟩
    have he := hs k j
    change B.stage τ j (splitSlots A B (H.path (H.columnCards x k).val (suffixTime A B j.castSucc))).2=
      (splitSlots A B (H.path (H.columnCards x k).val (suffixTime A B j.succ))).2 at he
    simpa only [hk] using he
  · intro hs k j
    exact hs (H.columnCards x k).val (H.columnCards x k).property j

/- The trajectory event is exactly the product of all child trajectory events. -/
theorem compatible_split (ω : (concat A B).Choices) :
    H.Compatible ω ↔
      (∀ y : B.Slot, (H.rowHoles y).Compatible (rowChoices A B ω y)) ∧
      (∀ x : A.Slot, (H.columnHoles x).Compatible (columnChoices A B ω x)) := by
  constructor
  · intro hω
    have hs := (H.compatible_iff_step ω).mp hω
    constructor
    · intro y
      apply ((H.rowHoles y).compatible_iff_step _).mpr
      apply (H.row_step_iff y _).mpr
      intro i hi j
      have he := congrArg (fun x => (splitSlots A B x).1) (hs i (Fin.castAdd B.b j))
      rw [stage_split_left] at he
      change A.stage (rowChoices A B ω (splitSlots A B (H.path i (prefixTime A B j.castSucc))).2) j
        (splitSlots A B (H.path i (prefixTime A B j.castSucc))).1=
        (splitSlots A B (H.path i (prefixTime A B j.succ))).1 at he
      rw [H.row_constant i j.castSucc,hi] at he
      exact he
    · intro x
      apply ((H.columnHoles x).compatible_iff_step _).mpr
      apply (H.column_step_iff x _).mpr
      intro i hi j
      have he := congrArg (fun x => (splitSlots A B x).2) (hs i (Fin.natAdd A.b j))
      rw [stage_split_right] at he
      change B.stage (columnChoices A B ω (splitSlots A B (H.path i (suffixTime A B j.castSucc))).1) j
        (splitSlots A B (H.path i (suffixTime A B j.castSucc))).2=
        (splitSlots A B (H.path i (suffixTime A B j.succ))).2 at he
      rw [H.column_constant i j.castSucc,hi] at he
      exact he
  · rintro ⟨hR,hC⟩
    have hr (y : B.Slot) := (H.row_step_iff y _).mp (((H.rowHoles y).compatible_iff_step _).mp (hR y))
    have hc (x : A.Slot) := (H.column_step_iff x _).mp (((H.columnHoles x).compatible_iff_step _).mp (hC x))
    apply (H.compatible_iff_step ω).mpr
    intro i j
    change Fin (A.b+B.b) at j
    induction j using Fin.addCases with
    | left j =>
      apply (splitSlots A B).injective
      rw [stage_split_left]
      apply Prod.ext
      · change A.stage (rowChoices A B ω (splitSlots A B (H.path i (prefixTime A B j.castSucc))).2) j
          (splitSlots A B (H.path i (prefixTime A B j.castSucc))).1=
          (splitSlots A B (H.path i (prefixTime A B j.succ))).1
        rw [H.row_constant i j.castSucc]
        exact hr (H.rowOf i) i rfl j
      · exact (H.row_constant i j.castSucc).trans (H.row_constant i j.succ).symm
    | right j =>
      apply (splitSlots A B).injective
      rw [stage_split_right]
      apply Prod.ext
      · exact (H.column_constant i j.castSucc).trans (H.column_constant i j.succ).symm
      · change B.stage (columnChoices A B ω (splitSlots A B (H.path i (suffixTime A B j.castSucc))).1) j
          (splitSlots A B (H.path i (suffixTime A B j.castSucc))).2=
          (splitSlots A B (H.path i (suffixTime A B j.succ))).2
        rw [H.column_constant i j.castSucc]
        exact hc (H.columnOf i) i rfl j

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid

/- The literal real line mass, without changing any conditioning. -/
def rawLineWeight (k : ℕ) (z : ℝ) (σ : Equiv.Perm (Cube k)) : ℝ :=
  (1-z)*(Fintype.card (Equiv.Perm (Cube k)) : ℝ)⁻¹ + z*binaryLaw k σ

lemma rawLineWeight_cast {k l : ℕ} (h : k=l) (z : ℝ) (σ : Equiv.Perm (Cube k)) :
    rawLineWeight k z σ=rawLineWeight l z ((Equiv.cast (congrArg Cube h)).permCongr σ) := by
  subst l
  rfl

lemma prefix_weight (A B : Grid) (ω : (concat A B).Choices) (z : ℝ) (i : Fin A.b) :
    (∏ L : (concat A B).Line (Fin.castAdd B.b i),
      rawLineWeight ((concat A B).bits (Fin.castAdd B.b i)) z (ω (Fin.castAdd B.b i) L))=
    ∏ y : B.Slot, ∏ L : A.Line i, rawLineWeight (A.bits i) z (rowChoices A B ω y i L) := by
  rw [← (rowLines A B i).prod_comp]
  rw [Fintype.prod_prod_type,Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro y _
  apply Finset.prod_congr rfl
  intro L _
  rw [rowChoices_apply]
  exact rawLineWeight_cast (concat_bits_left A B i) z _

lemma suffix_weight (A B : Grid) (ω : (concat A B).Choices) (z : ℝ) (i : Fin B.b) :
    (∏ L : (concat A B).Line (Fin.natAdd A.b i),
      rawLineWeight ((concat A B).bits (Fin.natAdd A.b i)) z (ω (Fin.natAdd A.b i) L))=
    ∏ x : A.Slot, ∏ L : B.Line i, rawLineWeight (B.bits i) z (columnChoices A B ω x i L) := by
  rw [← (columnLines A B i).prod_comp]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro x _
  apply Finset.prod_congr rfl
  intro L _
  rw [columnChoices_apply]
  exact rawLineWeight_cast (concat_bits_right A B i) z _

/- Complete independent choice mass factors into literal row and column masses. -/
theorem choiceWeight_split (A B : Grid) (ω : (concat A B).Choices) (z : ℝ) :
    (concat A B).choiceWeight z ω =
      (∏ y : B.Slot, A.choiceWeight z (rowChoices A B ω y))*
      (∏ x : A.Slot, B.choiceWeight z (columnChoices A B ω x)) := by
  have hr (G : Grid) (τ : G.Choices) : G.choiceWeight z τ=
      ∏ i : Fin G.b, ∏ L : G.Line i, rawLineWeight (G.bits i) z (τ i L) := by rfl
  rw [hr]
  erw [Fin.prod_univ_add]
  congr 1
  · trans ∏ i : Fin A.b, ∏ y : B.Slot, ∏ L : A.Line i,
        rawLineWeight (A.bits i) z (rowChoices A B ω y i L)
    · apply Finset.prod_congr rfl
      intro i _
      convert prefix_weight A B ω z i using 1
      congr 3
      exact Subsingleton.elim _ _
    · rw [Finset.prod_comm]
      rfl
  · trans ∏ i : Fin B.b, ∏ x : A.Slot, ∏ L : B.Line i,
        rawLineWeight (B.bits i) z (columnChoices A B ω x i L)
    · apply Finset.prod_congr rfl
      intro i _
      convert suffix_weight A B ω z i using 1
      congr 3
      exact Subsingleton.elim _ _
    · rw [Finset.prod_comm]
      rfl

end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid.Holes
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

def splitCompatibleChoices : {ω : (concat A B).Choices // H.Compatible ω} ≃
    ((∀ y : B.Slot, {τ : A.Choices // (H.rowHoles y).Compatible τ}) ×
     (∀ x : A.Slot, {τ : B.Choices // (H.columnHoles x).Compatible τ})) where
  toFun ω := ((fun y => ⟨rowChoices A B ω.val y,((H.compatible_split ω.val).mp ω.property).1 y⟩),
    fun x => ⟨columnChoices A B ω.val x,((H.compatible_split ω.val).mp ω.property).2 x⟩)
  invFun τ := ⟨(choicesSplit A B).symm ((fun y => (τ.1 y).val),(fun x => (τ.2 x).val)),by
    apply (H.compatible_split _).mpr
    constructor
    · intro y
      change (H.rowHoles y).Compatible ((choicesSplit A B ((choicesSplit A B).symm _)).1 y)
      rw [Equiv.apply_symm_apply]
      exact (τ.1 y).property
    · intro x
      change (H.columnHoles x).Compatible ((choicesSplit A B ((choicesSplit A B).symm _)).2 x)
      rw [Equiv.apply_symm_apply]
      exact (τ.2 x).property⟩
  left_inv ω := by
    apply Subtype.ext
    change (choicesSplit A B).symm (choicesSplit A B ω.val)=ω.val
    exact Equiv.symm_apply_apply _ _
  right_inv τ := by
    apply Prod.ext
    · funext y
      apply Subtype.ext
      change ((choicesSplit A B) ((choicesSplit A B).symm _)).1 y=(τ.1 y).val
      rw [Equiv.apply_symm_apply]
    · funext x
      apply Subtype.ext
      change ((choicesSplit A B) ((choicesSplit A B).symm _)).2 x=(τ.2 x).val
      rw [Equiv.apply_symm_apply]

lemma splitCompatibleChoices_weight (z : ℝ)
    (τ : (∀ y : B.Slot, {τ : A.Choices // (H.rowHoles y).Compatible τ}) ×
      (∀ x : A.Slot, {τ : B.Choices // (H.columnHoles x).Compatible τ})) :
    (concat A B).choiceWeight z (H.splitCompatibleChoices.symm τ).val=
      (∏ y, A.choiceWeight z (τ.1 y).val)*(∏ x, B.choiceWeight z (τ.2 x).val) := by
  rw [choiceWeight_split]
  have hr (y : B.Slot) : rowChoices A B (H.splitCompatibleChoices.symm τ).val y=(τ.1 y).val := by
    change (choicesSplit A B ((choicesSplit A B).symm _)).1 y=_
    rw [Equiv.apply_symm_apply]
  have hc (x : A.Slot) : columnChoices A B (H.splitCompatibleChoices.symm τ).val x=(τ.2 x).val := by
    change (choicesSplit A B ((choicesSplit A B).symm _)).2 x=_
    rw [Equiv.apply_symm_apply]
  simp_rw [hr,hc]

/- Exact product of all child path-event probabilities, for the real law. -/
theorem probability_split (z : ℝ) :
    H.probability z=(∏ y, (H.rowHoles y).probability z)*(∏ x, (H.columnHoles x).probability z) := by
  classical
  let (y : B.Slot) : Fintype {τ : A.Choices // (H.rowHoles y).Compatible τ} := Subtype.fintype _
  let (x : A.Slot) : Fintype {τ : B.Choices // (H.columnHoles x).Compatible τ} := Subtype.fintype _
  unfold probability
  rw [← H.splitCompatibleChoices.symm.sum_comp]
  simp_rw [H.splitCompatibleChoices_weight]
  rw [Fintype.sum_prod_type]
  dsimp only
  rw [← Finset.sum_mul_sum]
  congr 1
  · exact (Fintype.prod_sum (fun y (τ : {τ : A.Choices // (H.rowHoles y).Compatible τ}) =>
      A.choiceWeight z τ.val)).symm
  · exact (Fintype.prod_sum (fun x (τ : {τ : B.Choices // (H.columnHoles x).Compatible τ}) =>
      B.choiceWeight z τ.val)).symm

/- Literal normalized conditional mass factors; no trajectory is reweighted. -/
theorem conditionalWeight_split (z : ℝ) (ω : {ω : (concat A B).Choices // H.Compatible ω}) :
    (concat A B).choiceWeight z ω.val/H.probability z=
      (∏ y, A.choiceWeight z (rowChoices A B ω.val y)/(H.rowHoles y).probability z)*
      (∏ x, B.choiceWeight z (columnChoices A B ω.val x)/(H.columnHoles x).probability z) := by
  rw [choiceWeight_split,H.probability_split]
  rw [Finset.prod_div_distrib,Finset.prod_div_distrib]
  exact mul_div_mul_comm _ _ _ _

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Marked
variable {X Y I : Type*}
abbrev Free (x : I → X) := {z : X // ∀ i, z ≠ x i}

def freeEquiv (x : I → X) (y : I → Y) (e : X ≃ Y) (he : ∀ i, e (x i)=y i) :
    Free x ≃ Free y := e.subtypeEquiv (by
  intro z
  constructor
  · intro hz i hi
    apply hz i
    exact e.injective (hi.trans (he i).symm)
  · intro hz i hi
    apply hz i
    rw [hi,he])

lemma freeEquiv_apply (x : I → X) (y : I → Y) (e : X ≃ Y) (he : ∀ i, e (x i)=y i)
    (z : Free x) : (freeEquiv x y e he z).val=e z.val := rfl

def fix (x : I → X) : Subgroup (Equiv.Perm X) where
  carrier g := ∀ i, g (x i)=x i
  one_mem' _ := rfl
  mul_mem' := by
    intro g h hg hh i
    change g (h (x i))=x i
    rw [hh i,hg i]
  inv_mem' hg i := (Equiv.symm_apply_eq _).mpr (hg i).symm

def freePerm (x : I → X) : fix x →* Equiv.Perm (Free x) where
  toFun g := freeEquiv x x g.val g.property
  map_one' := by ext z; rfl
  map_mul' g h := by ext z; rfl

/- The honest symmetric group on the unmarked sites, including empty sets. -/
def freePermEquiv (x : I → X) : fix x ≃* Equiv.Perm (Free x) where
  toFun := freePerm x
  invFun σ := ⟨Equiv.Perm.ofSubtype σ,by
    intro i
    apply Equiv.Perm.ofSubtype_apply_of_not_mem
    simp only [not_forall,not_not]
    exact ⟨i,rfl⟩⟩
  left_inv g := by
    apply Subtype.ext
    ext z
    by_cases hz : ∀ i, z ≠ x i
    · rw [Equiv.Perm.ofSubtype_apply_of_mem _ hz]
      rfl
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hz]
      push Not at hz
      rcases hz with ⟨i,rfl⟩
      exact (g.property i).symm
  right_inv σ := by
    ext z
    change Equiv.Perm.ofSubtype σ z.val=(σ z).val
    exact Equiv.Perm.ofSubtype_apply_of_mem _ z.property
  map_mul' := (freePerm x).map_mul

lemma card_free [Fintype X] [Fintype I] (x : I → X) (hx : Function.Injective x) :
    Fintype.card (Free x)=Fintype.card X-Fintype.card I := by
  classical
  let e : Free x ≃ {z : X // ¬ z ∈ Set.range x} :=
    Equiv.subtypeEquivRight (fun z => by simp only [Set.mem_range,not_exists]; simp only [ne_eq,eq_comm])
  rw [Fintype.card_congr e,Fintype.card_subtype_compl]
  congr 1
  exact (Fintype.card_congr (Equiv.ofInjective x hx)).symm

end CoordinateSweeps.Marked

namespace CoordinateSweeps.Grid
@[simp] theorem card_slot (G : Grid) : Fintype.card G.Slot=G.size := by
  simp [Slot,size,Cube,Fintype.card_pi]

namespace Holes
variable {G : Grid} {h : ℕ}
abbrev FreeAt (H : G.Holes h) (t : Fin (G.b+1)) := Marked.Free (fun i => H.path i t)

def freeBoundary (H : G.Holes h) (ω : {ω : G.Choices // H.Compatible ω})
    (t : Fin (G.b+1)) : H.FreeAt 0 ≃ H.FreeAt t :=
  Marked.freeEquiv _ _ (G.boundary ω.val t.val) (fun i => ω.property i t)

lemma card_freeAt (H : G.Holes h) (t : Fin (G.b+1)) :
    Fintype.card (H.FreeAt t)=G.size-h := by
  have hh := Marked.card_free (fun i => H.path i t) (H.disjoint t)
  simp only [card_slot,Fintype.card_fin] at hh
  convert hh using 1
  congr 1
  exact Subsingleton.elim _ _

/- Literal target stabilizer isomorphism, not an assumed representation switch. -/
def stabilizerFreeEquiv (H : G.Holes h) : H.stabilizer ≃* Equiv.Perm (H.FreeAt 0) :=
  Marked.freePermEquiv (fun i => H.path i 0)

lemma stabilizerFreeEquiv_apply (H : G.Holes h) (g : H.stabilizer) (x : H.FreeAt 0) :
    (H.stabilizerFreeEquiv g x).val=g.val x.val := rfl

end Holes
end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid

def rowSweep (A B : Grid) (ω : B.Slot → A.Choices) : Equiv.Perm (concat A B).Slot :=
  Equiv.permCongr (splitSlots A B).symm (fiberPerm (fun y => A.sweep (ω y)))

def columnSweep (A B : Grid) (ω : A.Slot → B.Choices) : Equiv.Perm (concat A B).Slot :=
  Equiv.permCongr ((splitSlots A B).trans (Equiv.prodComm _ _)).symm
    (fiberPerm (fun x => B.sweep (ω x)))

lemma rowSweep_apply (A B : Grid) (ω : B.Slot → A.Choices) (x : (concat A B).Slot) :
    splitSlots A B (rowSweep A B ω x)=
      (A.sweep (ω (splitSlots A B x).2) (splitSlots A B x).1,(splitSlots A B x).2) := by
  unfold rowSweep
  simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
  rfl

lemma columnSweep_apply (A B : Grid) (ω : A.Slot → B.Choices) (x : (concat A B).Slot) :
    splitSlots A B (columnSweep A B ω x)=
      ((splitSlots A B x).1,B.sweep (ω (splitSlots A B x).1) (splitSlots A B x).2) := by
  unfold columnSweep
  simp only [Equiv.permCongr_apply,Equiv.symm_trans_apply,Equiv.symm_symm,Equiv.trans_apply,
    Equiv.apply_symm_apply]
  rfl

theorem sweep_eq_column_mul_row (A B : Grid) (ω : (concat A B).Choices) :
    (concat A B).sweep ω=columnSweep A B (columnChoices A B ω)*rowSweep A B (rowChoices A B ω) := by
  apply Equiv.ext
  intro x
  apply (splitSlots A B).injective
  have hr := rowSweep_apply A B (rowChoices A B ω) x
  have hc := columnSweep_apply A B (columnChoices A B ω) (rowSweep A B (rowChoices A B ω) x)
  have ht := congrArg (fun t : A.Slot × B.Slot =>
    (t.1,B.sweep (columnChoices A B ω t.1) t.2)) hr
  exact (sweep_split A B ω x).trans (hc.trans ht).symm

theorem rowSweep_eq_boundary (A B : Grid) (ω : (concat A B).Choices) :
    rowSweep A B (rowChoices A B ω)=(concat A B).boundary ω A.b := by
  apply Equiv.ext
  intro x
  apply (splitSlots A B).injective
  rw [rowSweep_apply,boundary_split_prefix A B ω x A.b le_rfl]
  rfl

namespace Holes
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)
abbrev RowChoices := ∀ y : B.Slot, {τ : A.Choices // (H.rowHoles y).Compatible τ}
abbrev ColumnChoices := ∀ x : A.Slot, {τ : B.Choices // (H.columnHoles x).Compatible τ}

def refPair (hf : H.Feasible) : H.RowChoices × H.ColumnChoices :=
  H.splitCompatibleChoices ⟨H.reference hf,H.reference_compatible hf⟩

def rowAction (τ : H.RowChoices) := rowSweep A B (fun y => (τ y).val)
def columnAction (τ : H.ColumnChoices) := columnSweep A B (fun x => (τ x).val)

lemma split_choice_sweep (τ : H.RowChoices × H.ColumnChoices) :
    (concat A B).sweep (H.splitCompatibleChoices.symm τ).val=H.columnAction τ.2*H.rowAction τ.1 := by
  rw [sweep_eq_column_mul_row]
  change columnSweep A B ((choicesSplit A B ((choicesSplit A B).symm _)).2)*
    rowSweep A B ((choicesSplit A B ((choicesSplit A B).symm _)).1)=_
  rw [Equiv.apply_symm_apply]
  rfl

lemma rowAction_marked (hf : H.Feasible) (τ : H.RowChoices) (i : Fin h) :
    H.rowAction τ (H.path i 0)=H.path i (suffixTime A B 0) := by
  let ω : {ω : (concat A B).Choices // H.Compatible ω} :=
    H.splitCompatibleChoices.symm (τ,(H.refPair hf).2)
  have he : H.rowAction τ=rowSweep A B (rowChoices A B ω.val) := by
    change rowSweep A B (fun y => (τ y).val)=rowSweep A B (fun y =>
      ((choicesSplit A B) ((choicesSplit A B).symm _)).1 y)
    rw [Equiv.apply_symm_apply]
  rw [he,rowSweep_eq_boundary]
  exact ω.property i (suffixTime A B 0)

lemma columnAction_marked (hf : H.Feasible) (τ : H.ColumnChoices) (i : Fin h) :
    H.columnAction τ (H.path i (suffixTime A B 0))=H.path i (Fin.last _) := by
  let ω : {ω : (concat A B).Choices // H.Compatible ω} :=
    H.splitCompatibleChoices.symm ((H.refPair hf).1,τ)
  have hs := H.split_choice_sweep ((H.refPair hf).1,τ)
  have hr := H.rowAction_marked hf (H.refPair hf).1 i
  have he := ω.property i (Fin.last _)
  change (concat A B).sweep ω.val (H.path i 0)=_ at he
  rw [hs] at he
  change H.columnAction τ (H.rowAction (H.refPair hf).1 (H.path i 0))=_ at he
  rwa [hr] at he

abbrev JunctionFix := Marked.fix (fun i => H.path i (suffixTime A B 0))

def rowResidual (hf : H.Feasible) (τ : H.RowChoices) : H.JunctionFix :=
  ⟨H.rowAction τ*(H.rowAction (H.refPair hf).1)⁻¹,by
    intro i
    change H.rowAction τ ((H.rowAction (H.refPair hf).1).symm (H.path i (suffixTime A B 0)))=_
    rw [← H.rowAction_marked hf (H.refPair hf).1 i,Equiv.symm_apply_apply,H.rowAction_marked hf τ i]⟩

def columnResidual (hf : H.Feasible) (τ : H.ColumnChoices) : H.JunctionFix :=
  ⟨(H.columnAction (H.refPair hf).2)⁻¹*H.columnAction τ,by
    intro i
    change (H.columnAction (H.refPair hf).2).symm (H.columnAction τ (H.path i (suffixTime A B 0)))=_
    rw [H.columnAction_marked hf τ i,← H.columnAction_marked hf (H.refPair hf).2 i,Equiv.symm_apply_apply]⟩

end Holes
end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid.Holes
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

/- Move the target's reference identification to the actual junction layer. -/
def junctionEquiv (hf : H.Feasible) : H.stabilizer ≃* H.JunctionFix where
  toFun g := ⟨H.rowAction (H.refPair hf).1*g.val*(H.rowAction (H.refPair hf).1)⁻¹,by
    intro i
    change H.rowAction (H.refPair hf).1 (g.val
      ((H.rowAction (H.refPair hf).1).symm (H.path i (suffixTime A B 0))))=_
    rw [← H.rowAction_marked hf (H.refPair hf).1 i,Equiv.symm_apply_apply,g.property i]
    exact H.rowAction_marked hf (H.refPair hf).1 i⟩
  invFun g := ⟨(H.rowAction (H.refPair hf).1)⁻¹*g.val*H.rowAction (H.refPair hf).1,by
    intro i
    change (H.rowAction (H.refPair hf).1).symm
      (g.val (H.rowAction (H.refPair hf).1 (H.path i 0)))=_
    rw [H.rowAction_marked hf (H.refPair hf).1 i,g.property i]
    exact (Equiv.symm_apply_eq _).mpr (H.rowAction_marked hf (H.refPair hf).1 i).symm⟩
  left_inv g := by
    apply Subtype.ext
    change (H.rowAction (H.refPair hf).1)⁻¹*
      (H.rowAction (H.refPair hf).1*g.val*(H.rowAction (H.refPair hf).1)⁻¹)*H.rowAction (H.refPair hf).1=g.val
    group
  right_inv g := by
    apply Subtype.ext
    change H.rowAction (H.refPair hf).1*
      ((H.rowAction (H.refPair hf).1)⁻¹*g.val*H.rowAction (H.refPair hf).1)*(H.rowAction (H.refPair hf).1)⁻¹=g.val
    group
  map_mul' g k := by
    apply Subtype.ext
    change H.rowAction (H.refPair hf).1*(g.val*k.val)*(H.rowAction (H.refPair hf).1)⁻¹=
      (H.rowAction (H.refPair hf).1*g.val*(H.rowAction (H.refPair hf).1)⁻¹)*
      (H.rowAction (H.refPair hf).1*k.val*(H.rowAction (H.refPair hf).1)⁻¹)
    group

lemma sweep_refPair (hf : H.Feasible) :
    (concat A B).sweep (H.reference hf)=H.columnAction (H.refPair hf).2*H.rowAction (H.refPair hf).1 := by
  simpa only [refPair,Equiv.symm_apply_apply] using H.split_choice_sweep (H.refPair hf)

lemma junction_residual (hf : H.Feasible) (ω : {ω : (concat A B).Choices // H.Compatible ω}) :
    H.junctionEquiv hf (H.residual hf ω)=
      H.columnResidual hf (H.splitCompatibleChoices ω).2*H.rowResidual hf (H.splitCompatibleChoices ω).1 := by
  apply Subtype.ext
  change H.rowAction (H.refPair hf).1*(((concat A B).sweep (H.reference hf))⁻¹*
    (concat A B).sweep ω.val)*(H.rowAction (H.refPair hf).1)⁻¹=_
  have he : (concat A B).sweep ω.val=H.columnAction (H.splitCompatibleChoices ω).2*
      H.rowAction (H.splitCompatibleChoices ω).1 := by
    simpa only [Equiv.symm_apply_apply] using H.split_choice_sweep (H.splitCompatibleChoices ω)
  rw [H.sweep_refPair hf,he]
  change _=((H.columnAction (H.refPair hf).2)⁻¹*H.columnAction (H.splitCompatibleChoices ω).2)*
    (H.rowAction (H.splitCompatibleChoices ω).1*(H.rowAction (H.refPair hf).1)⁻¹)
  group

instance rowChoicesFintype : Fintype H.RowChoices := by
  letI (y : B.Slot) : Fintype {ω : A.Choices // (H.rowHoles y).Compatible ω} := Subtype.fintype _
  unfold RowChoices
  infer_instance

instance columnChoicesFintype : Fintype H.ColumnChoices := by
  letI (x : A.Slot) : Fintype {ω : B.Choices // (H.columnHoles x).Compatible ω} := Subtype.fintype _
  unfold ColumnChoices
  infer_instance

/- Arbitrary matrix representations may be used: the equality is at the law level. -/
def rowAverage {n : Type*} [Fintype n] [DecidableEq n] (hf : H.Feasible) (z : ℝ)
    (τ : H.JunctionFix →* Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ ω : H.RowChoices, ((∏ y, A.choiceWeight z (ω y).val/(H.rowHoles y).probability z : ℝ) : ℂ) •
    τ (H.rowResidual hf ω)

def columnAverage {n : Type*} [Fintype n] [DecidableEq n] (hf : H.Feasible) (z : ℝ)
    (τ : H.JunctionFix →* Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ ω : H.ColumnChoices, ((∏ x, B.choiceWeight z (ω x).val/(H.columnHoles x).probability z : ℝ) : ℂ) •
    τ (H.columnResidual hf ω)

/- Exact factorization of the faithful conditional matrix average at the
junction. -/
theorem junction_average_split {n : Type*} [Fintype n] [DecidableEq n]
    (hf : H.Feasible) (z : ℝ) (τ : H.JunctionFix →* Matrix n n ℂ) :
    (∑ ω : {ω : (concat A B).Choices // H.Compatible ω},
      (((concat A B).choiceWeight z ω.val/H.probability z : ℝ) : ℂ) •
        τ (H.junctionEquiv hf (H.residual hf ω)))=
      H.columnAverage hf z τ*H.rowAverage hf z τ := by
  classical
  let (y : B.Slot) : Fintype {ω : A.Choices // (H.rowHoles y).Compatible ω} := Subtype.fintype _
  let (x : A.Slot) : Fintype {ω : B.Choices // (H.columnHoles x).Compatible ω} := Subtype.fintype _
  rw [← H.splitCompatibleChoices.symm.sum_comp]
  simp_rw [H.junction_residual,Equiv.apply_symm_apply,map_mul,H.conditionalWeight_split,
    Complex.ofReal_mul]
  unfold columnAverage rowAverage
  rw [Matrix.sum_mul]
  simp_rw [Matrix.mul_sum,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro r _
  have he := H.splitCompatibleChoices.apply_symm_apply (r,c)
  have hr : rowChoices A B (H.splitCompatibleChoices.symm (r,c)).val=fun y => (r y).val := by
    change ((choicesSplit A B) ((choicesSplit A B).symm _)).1=_
    rw [Equiv.apply_symm_apply]
  have hc : columnChoices A B (H.splitCompatibleChoices.symm (r,c)).val=fun x => (c x).val := by
    change ((choicesSplit A B) ((choicesSplit A B).symm _)).2=_
    rw [Equiv.apply_symm_apply]
  simp only [hr,hc]
  rw [mul_comm]

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps

namespace Grid.Holes

variable {G : Grid} {h : ℕ}

/- Average of the remaining random bijection, conditioned on the entire paths,
not only endpoints. The reference affects only unitary identifications. -/
def conditionalAverage (H : G.Holes h) (hf : H.Feasible) (z : ℝ)
    (ρ : UnitaryIrrep H.stabilizer) : Matrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ :=
  (H.probability z : ℂ)⁻¹ •
    ∑ ω : {ω : G.Choices // H.Compatible ω},
      (G.choiceWeight z ω.val : ℂ) • ρ.matrix (H.residual hf ω)

theorem probability_pos (H : G.Holes h) (hf : H.Feasible) {z : ℝ}
    (hz : 0 ≤ z) (hz' : z < 1) : 0 < H.probability z := by
  let : Nonempty {ω : G.Choices // H.Compatible ω} :=
    ⟨⟨H.reference hf, H.reference_compatible hf⟩⟩
  apply Finset.sum_pos
  · intro ω _
    exact G.choiceWeight_pos hz hz' ω.val
  · exact Finset.univ_nonempty

theorem conditionalAverage_eq_sum (H : G.Holes h) (hf : H.Feasible) (z : ℝ)
    (ρ : UnitaryIrrep H.stabilizer) :
    H.conditionalAverage hf z ρ =
      ∑ ω : {ω : G.Choices // H.Compatible ω},
        ((G.choiceWeight z ω.val / H.probability z : ℝ) : ℂ) •
          ρ.matrix (H.residual hf ω) := by
  simp only [conditionalAverage, Finset.smul_sum, smul_smul, div_eq_mul_inv,
    Complex.ofReal_mul, Complex.ofReal_inv, mul_comm]

theorem conditionalAverage_norm_le (H : G.Holes h) (hf : H.Feasible) {z : ℝ}
    (hz : 0 ≤ z) (hz' : z < 1) (ρ : UnitaryIrrep H.stabilizer) :
    ‖H.conditionalAverage hf z ρ‖ ≤ 1 := by
  let : NeZero ρ.dimension := ⟨ρ.positive.ne'⟩
  rw [H.conditionalAverage_eq_sum hf z ρ]
  apply unitary_average_norm_le
  · intro ω
    exact div_nonneg (G.choiceWeight_pos hz hz' ω.val).le (H.probability_pos hf hz hz').le
  · rw [← Finset.sum_div]
    exact div_self (H.probability_pos hf hz hz').ne'
  · intro ω
    exact ρ.unitary (H.residual hf ω)

theorem conditionalMoment_nonneg (H : G.Holes h) (hf : H.Feasible) (z : ℝ)
    (ρ : UnitaryIrrep H.stabilizer) (q : ℕ) :
    0 ≤ schattenMoment q (H.conditionalAverage hf z ρ) :=
  trace_moment_nonneg _ _

theorem conditionalMoment_le_dimension (H : G.Holes h) (hf : H.Feasible) {z : ℝ}
    (hz : 0 ≤ z) (hz' : z < 1) (ρ : UnitaryIrrep H.stabilizer) (q : ℕ) :
    schattenMoment q (H.conditionalAverage hf z ρ) ≤ ρ.dimension := by
  let : NeZero ρ.dimension := ⟨ρ.positive.ne'⟩
  apply (trace_moment_le _ q).trans
  have hn := H.conditionalAverage_norm_le hf hz hz' ρ
  have hp : ‖H.conditionalAverage hf z ρ‖^(2*q) ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) hn
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) hp

end Grid.Holes

/- Source constants a=1/100, c0=e0=a/100. -/
def a : ℝ := 1 / 100
def c0 : ℝ := a / 100
def e0 : ℝ := a / 100
def c (s : ℕ) : ℝ := c0 + 1 / Real.sqrt (Real.log s)
def e (s : ℕ) : ℝ := e0 - 1 / Real.sqrt (Real.log s)

/- Natural logarithm with the manuscript's log zero = minus infinity. -/
def logMoment (t : ℝ) : EReal := if t = 0 then ⊥ else (Real.log t : EReal)

/- Faithful conditional main target; R=2^r. The harmless strengthening z_*≤1/2
makes the probability-law range explicit. -/
def ConditionalMain : Prop :=
  ∃ (r q : ℕ) (zStar : ℝ), 1 ≤ r ∧ 1 ≤ q ∧ 0 < zStar ∧ zStar ≤ 1 / ((2 : ℕ) : ℝ) ∧
    ∀ (G : Grid), G.Allowed r → ∀ (h : ℕ) (H : G.Holes h) (hf : H.Feasible),
    ∀ z ∈ Set.Icc 0 zStar, ∀ ρ : UnitaryIrrep H.stabilizer,
      logMoment (schattenMoment q (H.conditionalAverage hf z ρ)) ≤
        ((-c G.size * Real.log ρ.dimension + e G.size * h * Real.log G.size - H.cost : ℝ) : EReal)

end CoordinateSweeps

end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
