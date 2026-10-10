import OAI.NumberTheory.Ostmann.Arithmetic.HistoryOccurrenceLevels
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepeatedRenamingBasic
import OAI.NumberTheory.Ostmann.Construction.CanonicalSourceLabels

namespace OAI

noncomputable section
namespace Ostmann.Construction.CanonicalOccurrenceTransport
open Arithmetic.HistoryOccurrenceVariables Arithmetic.HistorySymbolicEncoding
open Characters.RationalHistory

@[reducible] def Internal (seed : List SourceSlot) : ℕ→Type
  | 0 => Empty
  | l+1 => Fin (Template.extracted (l+1) (Template.current seed l)).length ⊕
      (Internal seed l ⊕ Internal seed l)

@[reducible] def Coordinate (seed : List SourceSlot) (l : ℕ) :=
  Bool ⊕ (Fin (Template.current seed l).length ⊕ Internal seed l)

instance internalFintype (seed : List SourceSlot) : (l:ℕ)→Fintype (Internal seed l)
  | 0 => inferInstanceAs (Fintype Empty)
  | l+1 => by
    letI := internalFintype seed l
    exact inferInstanceAs (Fintype (Fin (Template.extracted (l+1) (Template.current seed l)).length ⊕
      (Internal seed l ⊕ Internal seed l)))

instance coordinateFintype (seed : List SourceSlot) (l : ℕ) : Fintype (Coordinate seed l) :=
  inferInstanceAs (Fintype (Bool ⊕ (Fin (Template.current seed l).length ⊕ Internal seed l)))

lemma root_matches {seed : List SourceSlot} {l : ℕ} {h : History l}
    (hh : TreeSourceLabels seed h) : Template.Matches (Template.current seed l) h.root.small := by
  cases h with
  | leaf a => exact hh
  | node a p u hp hm left right => exact hh.1

def internalEquiv (seed : List SourceSlot) : {l:ℕ}→(h:History l)→
    TreeSourceLabels seed h → Internal seed l ≃ InternalKey h
  | _, .leaf _, _ => Equiv.refl Empty
  | _, .node _ _ _ _ _ left right, hh =>
      Equiv.sumCongr (finCongr (Template.matches_length hh.2.2.2.1).symm)
        (Equiv.sumCongr (internalEquiv seed left hh.2.2.2.2.1)
          (internalEquiv seed right hh.2.2.2.2.2))

def coordinateEquiv (seed : List SourceSlot) {l : ℕ} (h : History l)
    (hh : TreeSourceLabels seed h) : Coordinate seed l ≃ Key h :=
  Equiv.sumCongr (Equiv.refl Bool)
    (Equiv.sumCongr (finCongr (Template.matches_length (root_matches hh)).symm)
      (internalEquiv seed h hh))

def internalLevel (seed : List SourceSlot) : {l:ℕ}→Internal seed l→ℕ
  | 0, i => Empty.elim i
  | l+1, .inl _ => l+1
  | _+1, .inr (.inl i) => internalLevel seed i
  | _+1, .inr (.inr i) => internalLevel seed i

def coordinateLevel (seed : List SourceSlot) (l : ℕ) : Coordinate seed l→ℕ :=
  Sum.elim (fun _ => l+1) (Sum.elim (fun _ => l+1) (internalLevel seed))

@[simp] theorem internalEquiv_level (seed : List SourceSlot) {l : ℕ}
    (h : History l) (hh : TreeSourceLabels seed h) (i : Internal seed l) :
    Arithmetic.HistoryOccurrenceVariables.internalLevel h (internalEquiv seed h hh i)=
      internalLevel seed i := by
  induction h with
  | leaf a => exact Empty.elim i
  | node a p u hp hm left right ihl ihr =>
    rcases i with i | i | i
    · rfl
    · exact ihl hh.2.2.2.2.1 i
    · exact ihr hh.2.2.2.2.2 i

@[simp] theorem coordinateEquiv_level (seed : List SourceSlot) {l : ℕ}
    (h : History l) (hh : TreeSourceLabels seed h) (i : Coordinate seed l) :
    keyLevel h (coordinateEquiv seed h hh i)=coordinateLevel seed l i := by
  rcases i with b | i | i
  · rfl
  · rfl
  · exact internalEquiv_level seed h hh i

@[simp] theorem root_plus_atom (seed : List SourceSlot) {l : ℕ}
    (h : History l) (hh : TreeSourceLabels seed h) :
    (rootExpr h).plus.rename (coordinateEquiv seed h hh).symm=Expr.atom (.inl false) := rfl

@[simp] theorem root_minus_atom (seed : List SourceSlot) {l : ℕ}
    (h : History l) (hh : TreeSourceLabels seed h) :
    (rootExpr h).minus.rename (coordinateEquiv seed h hh).symm=Expr.atom (.inl true) := rfl

@[simp] theorem root_small_atom (seed : List SourceSlot) {l : ℕ}
    (h : History l) (hh : TreeSourceLabels seed h)
    (i : Fin (Template.current seed l).length) :
    ((rootExpr h).small (finCongr (Template.matches_length (root_matches hh)).symm i)).rename
      (coordinateEquiv seed h hh).symm=Expr.atom (.inr (.inl i)) := by
  simp [rootExpr,Expr.rename,coordinateEquiv]

@[simp] theorem compensation_atom (seed : List SourceSlot) {l : ℕ}
    (h : History l) (hh : TreeSourceLabels seed h) (i : Internal seed l) :
    (compensationExpr h (internalEquiv seed h hh i)).rename (coordinateEquiv seed h hh).symm=
      Expr.atom (.inr (.inr i)) := by
  simp [compensationExpr,Expr.rename,coordinateEquiv]

def decodedCoordinateEquiv (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small) :
    Coordinate seed l ≃ Key (decodeHistory sources seed V l a c) :=
  coordinateEquiv seed _ (decoded_tree_source_labels sources seed V l a c ha)

end Ostmann.Construction.CanonicalOccurrenceTransport

end

end OAI
