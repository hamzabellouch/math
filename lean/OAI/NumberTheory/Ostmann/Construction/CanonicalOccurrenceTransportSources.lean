import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSlots
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportKeys

namespace OAI

noncomputable section
namespace Ostmann.Construction.CanonicalOccurrenceTransport
open Arithmetic.HistoryOccurrenceVariables Arithmetic.HistorySymbolicEncoding

def sourceOfSlot (z : SmallSlot) : SourceSlot := ⟨z.role,z.origin⟩

lemma matches_get_source {T : List SourceSlot} {xs : List SmallSlot}
    (h : Template.Matches T xs) (i : Fin T.length) :
    sourceOfSlot (xs.get (finCongr (Template.matches_length h).symm i))=T.get i := by
  have hi : i.val<xs.length := by simpa only [Template.matches_length h] using i.isLt
  have hh := congrArg (fun z : List (SlotRole×ℕ) => z[i.val]?) h
  have he : ((xs.get (finCongr (Template.matches_length h).symm i)).role,
      (xs.get (finCongr (Template.matches_length h).symm i)).origin)=
      ((T.get i).role,(T.get i).origin) := by
    simpa [List.getElem?_eq_getElem,hi,i.isLt] using hh
  calc
    _ = SourceSlot.mk (T.get i).role (T.get i).origin :=
      congrArg₂ SourceSlot.mk (congrArg Prod.fst he) (congrArg Prod.snd he)
    _ = T.get i := by cases T.get i; rfl

def internalSource (seed : List SourceSlot) : {l:ℕ}→Internal seed l→SourceSlot
  | _+1, .inl i => (Template.extracted _ (Template.current seed _)).get i
  | _+1, .inr (.inl i) => internalSource seed i
  | _+1, .inr (.inr i) => internalSource seed i

def coordinateSource (seed : List SourceSlot) (l : ℕ) : Coordinate seed l→Option SourceSlot
  | .inl _ => none
  | .inr (.inl i) => some ((Template.current seed l).get i)
  | .inr (.inr i) => some (internalSource seed i)

@[simp] theorem internalEquiv_source (seed : List SourceSlot) {l : ℕ}
    (h : History l) (hh : TreeSourceLabels seed h) (i : Internal seed l) :
    sourceOfSlot (internalSlot h (internalEquiv seed h hh i))=internalSource seed i := by
  induction h with
  | leaf a => exact Empty.elim i
  | node a p u hp hm left right ihl ihr =>
    rcases i with i | i | i
    · exact matches_get_source hh.2.2.2.1 i
    · exact ihl hh.2.2.2.2.1 i
    · exact ihr hh.2.2.2.2.2 i

@[simp] theorem coordinateEquiv_source (seed : List SourceSlot) {l : ℕ}
    (h : History l) (hh : TreeSourceLabels seed h) (i : Coordinate seed l) :
    (independentSlot h (coordinateEquiv seed h hh i)).map sourceOfSlot=
      coordinateSource seed l i := by
  rcases i with b | i | i
  · rfl
  · exact congrArg some (matches_get_source (root_matches hh) i)
  · exact congrArg some (internalEquiv_source seed h hh i)

def coordinateSample (seed : List SourceSlot) {l : ℕ} (h : History l)
    (hh : TreeSourceLabels seed h) : Coordinate seed l→ℤ :=
  integerSample h ∘ coordinateEquiv seed h hh

@[simp] theorem coordinateSample_giant (seed : List SourceSlot) {l : ℕ}
    (h : History l) (hh : TreeSourceLabels seed h) (b : Bool) :
    coordinateSample seed h hh (.inl b)=
      (if b then h.root.giantMinus else h.root.giantPlus : ℕ) := by
  cases b <;> rfl

theorem coordinate_typed_equality_iff (seed : List SourceSlot) {l : ℕ}
    (h : History l) (hh : TreeSourceLabels seed h) (i j : Coordinate seed l) :
    (keyLevel h (coordinateEquiv seed h hh i)=keyLevel h (coordinateEquiv seed h hh j) ∧
      integerSample h (coordinateEquiv seed h hh i)=integerSample h (coordinateEquiv seed h hh j)) ↔
    coordinateLevel seed l i=coordinateLevel seed l j ∧
      coordinateSample seed h hh i=coordinateSample seed h hh j := by
  simp only [coordinateEquiv_level,coordinateSample,Function.comp_apply]

end Ostmann.Construction.CanonicalOccurrenceTransport

end

end OAI
