import OAI.Combinatorics.SnakyCertificate.Table

namespace OAI

namespace SnakyCertificate

structure RowData where
  A : Finset Cell
  H : Finset Cell
  height : ℕ
  deriving DecidableEq

def emptyRow : RowData := ⟨∅, ∅, 0⟩

def baseRow (i : Fin 6) : RowData := ⟨baseRequired i, baseEnvelope i, 1⟩

def placeRow (t : Term) (d : RowData) : RowData :=
  ⟨d.A.image (placement t.rotation t.shift),
   d.H.image (placement t.rotation t.shift), d.height⟩

def unionA (ds : List RowData) : Finset Cell := (ds.map RowData.A).foldr (· ∪ ·) ∅

def unionH (ds : List RowData) : Finset Cell := (ds.map RowData.H).foldr (· ∪ ·) ∅

def commonH (ds : List RowData) : Finset Cell :=
  match ds with
  | [] => ∅
  | d :: rest => (rest.map RowData.H).foldr (· ∩ ·) d.H

def forkRow (ds : List RowData) : RowData :=
  ⟨(unionA ds ∪ commonH ds).erase origin,
   insert origin (unionH ds), 1 + (ds.map RowData.height).foldr max 0⟩

def rowAt (i : ℕ) : RowData :=
  if h : i < 6 then baseRow ⟨i, h⟩ else
    forkRow ((entryAt i).terms.map fun t =>
      placeRow t (if _ : t.child < i then rowAt t.child else emptyRow))
termination_by i

def Output (i : ℕ) (p : Cell) (size height : ℕ) (omitted : Set Cell) : Prop :=
  (rowAt i).A = {p} ∧ (rowAt i).H.card = size ∧ (rowAt i).height = height ∧
  Disjoint (↑(rowAt i).H : Set Cell) omitted

def AllRows : Prop := ∀ i, i < 616 →
  (rowAt i).A ⊆ (rowAt i).H ∧ origin ∈ (rowAt i).H ∧
  origin ∉ (rowAt i).A ∧ (rowAt i).height ≤ 34

end SnakyCertificate

end OAI
