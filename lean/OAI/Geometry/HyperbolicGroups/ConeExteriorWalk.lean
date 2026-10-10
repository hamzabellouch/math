import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeCellWalk
import OAI.Geometry.HyperbolicGroups.ExteriorTarget
import OAI.Geometry.HyperbolicGroups.PolygonBoundaryList
import OAI.Geometry.HyperbolicGroups.PolygonDiskProducer

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Dart n w)
  (closed : ∀ i, start n w (word (finRotate ell i)) = start n w (rev n w (word i)))
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)

abbrev OutsideCellSide := ((boundary n w d).withOutside ell hell word closed).Side
abbrev exteriorWalkTarget := (walkTarget n w d c hc f).withExterior ell hell word closed
abbrev exteriorWalkFrozen := (walkTarget n w d c hc f).exteriorFrozen ell hell word closed
  (walkFrozenTarget n w d c hc f)

def exteriorCellStep : OutsideCellSide n w d ell hell word closed →
    (WalkStep n w d ⊕ (walkTarget n w d c hc f).ExteriorSide ell hell word closed)
  | ⟨.inl a,b,i⟩ => .inl (cellWalkStep n w d ⟨a,b,i⟩)
  | ⟨.inr a,b,i⟩ => .inr ⟨a,b,i⟩

lemma exteriorCellStep_label (s : OutsideCellSide n w d ell hell word closed) :
    (exteriorWalkTarget n w d ell hell word closed c hc f).label
      (exteriorCellStep n w d ell hell word closed c hc f s) =
      ((boundary n w d).withOutside ell hell word closed).sideLabel s := by
  rcases s with ⟨a,b,i⟩
  rcases a with a | a
  · exact cellWalkStep_label n w d ⟨a,b,i⟩
  · rfl

lemma exteriorCellStep_kind (s : OutsideCellSide n w d ell hell word closed) :
    (exteriorWalkTarget n w d ell hell word closed c hc f).kind
      (exteriorCellStep n w d ell hell word closed c hc f
        (((boundary n w d).withOutside ell hell word closed).next s)) =
    (exteriorWalkTarget n w d ell hell word closed c hc f).kind
      (exteriorCellStep n w d ell hell word closed c hc f s) := by
  rcases s with ⟨a,b,i⟩
  rcases a with a | a
  · exact congrArg Sum.inl (cellWalkStep_kind n w d ⟨a,b,i⟩)
  · rfl

lemma exteriorCellStep_closed (s : OutsideCellSide n w d ell hell word closed) :
    (exteriorWalkTarget n w d ell hell word closed c hc f).front
      (exteriorCellStep n w d ell hell word closed c hc f
        (((boundary n w d).withOutside ell hell word closed).next s)) =
    (exteriorWalkTarget n w d ell hell word closed c hc f).back
      (exteriorCellStep n w d ell hell word closed c hc f s) := by
  rcases s with ⟨a,b,i⟩
  rcases a with a | a
  · exact congrArg Sum.inl (cellWalkStep_closed n w d ⟨a,b,i⟩)
  · exact congrArg Sum.inr
      (((walkTarget n w d c hc f).exteriorBoundary ell hell word closed).next_start ⟨a,b,i⟩)

lemma exteriorCellStep_frozen_next (s : OutsideCellSide n w d ell hell word closed)
    (h : (exteriorWalkTarget n w d ell hell word closed c hc f).free
      ((exteriorWalkTarget n w d ell hell word closed c hc f).kind
        (exteriorCellStep n w d ell hell word closed c hc f s)) = false) :
    exteriorCellStep n w d ell hell word closed c hc f
      (((boundary n w d).withOutside ell hell word closed).next s) =
    (exteriorWalkFrozen n w d ell hell word closed c hc f).next
      (exteriorCellStep n w d ell hell word closed c hc f s) := by
  rcases s with ⟨a,b,i⟩
  rcases a with a | a
  · exact congrArg Sum.inl (cellWalkStep_frozen_next n w d ⟨a,b,i⟩ h)
  · rfl

lemma exteriorCellStep_frozen_inj {s t : OutsideCellSide n w d ell hell word closed}
    (h : (exteriorWalkTarget n w d ell hell word closed c hc f).free
      ((exteriorWalkTarget n w d ell hell word closed c hc f).kind
        (exteriorCellStep n w d ell hell word closed c hc f s)) = false)
    (he : exteriorCellStep n w d ell hell word closed c hc f s =
      exteriorCellStep n w d ell hell word closed c hc f t) : s = t := by
  rcases s with ⟨a,b,i⟩
  rcases t with ⟨a',b',i'⟩
  rcases a with a | a <;> rcases a' with a' | a'
  · have hh := cellWalkStep_frozen_inj n w d h (Sum.inl.inj he)
    have ha := (Sigma.mk.inj hh).1
    subst a'
    have hi := eq_of_heq (Sigma.mk.inj hh).2
    cases hi
    rfl
  · cases he
  · cases he
  · have hh := Sum.inr.inj he
    have ha := (Sigma.mk.inj hh).1
    subst a'
    have hi := eq_of_heq (Sigma.mk.inj hh).2
    cases hi
    rfl

variable (weight : Cell n w d → A)
abbrev exteriorCellTarget := (boundary n w d).outsideTarget ell hell word closed weight
  (isApex n w) (radial n w)
universe u
variable (P : CellPicture.{u} (exteriorCellTarget n w d ell hell word closed weight))

/-- Transfer keeps the raw diagram and arbitrary outside word literally,
while opening top polygon steps to the checked cone surgeries. -/
def exteriorCellToWalk : WalkPicture.{u} (exteriorWalkTarget n w d ell hell word closed c hc f) where
  Dart := P.Dart
  pairing := P.pairing
  index := exteriorCellStep n w d ell hell word closed c hc f ∘ P.index
  closed := by
    intro x
    change (exteriorWalkTarget n w d ell hell word closed c hc f).front
      (exteriorCellStep n w d ell hell word closed c hc f (P.index (P.pairing.face x))) = _
    rw [P.mapped.commute]
    exact exteriorCellStep_closed n w d ell hell word closed c hc f _
  kind := by
    intro x
    change (exteriorWalkTarget n w d ell hell word closed c hc f).kind
      (exteriorCellStep n w d ell hell word closed c hc f (P.index (P.pairing.face x))) = _
    rw [P.mapped.commute]
    exact exteriorCellStep_kind n w d ell hell word closed c hc f _
  paired := by
    intro x
    change (exteriorWalkTarget n w d ell hell word closed c hc f).label
      (exteriorCellStep n w d ell hell word closed c hc f (P.index (P.pairing.edge x))) =
      rev n w ((exteriorWalkTarget n w d ell hell word closed c hc f).label
        (exteriorCellStep n w d ell hell word closed c hc f (P.index x)))
    rw [exteriorCellStep_label,exteriorCellStep_label]
    exact P.respects.2 x
  genusZero := P.genusZero

lemma exteriorCellToWalk_frozen :
    (exteriorCellToWalk n w d ell hell word closed c hc f weight P).FrozenMapped
      (exteriorWalkFrozen n w d ell hell word closed c hc f) := by
  constructor
  · intro x
    exact (congrArg (exteriorCellStep n w d ell hell word closed c hc f)
      (P.mapped.commute x.val)).trans
      (exteriorCellStep_frozen_next n w d ell hell word closed c hc f _ x.property)
  · intro x y hxy he
    apply Subtype.ext
    apply P.mapped.injective
    · exact semiconj_perm_sameCycle
        (j := fun x : (exteriorCellToWalk n w d ell hell word closed c hc f weight P).FrozenDart => (x.val : P.Dart))
        (t := P.pairing.face) (fun _ => rfl) hxy
    · exact exteriorCellStep_frozen_inj n w d ell hell word closed c hc f x.property he

lemma exteriorCellToWalk_tag (xs : List P.Dart)
    (hp : ∀ x, (boundary n w d).outsideTag ell hell word closed (P.index x) =
      if x ∈ xs then some true else none) :
    ∀ x s, (exteriorCellToWalk n w d ell hell word closed c hc f weight P).index x = .inr s →
      s.2.1 = true := by
  intro x s he
  have hx := hp x
  cases hxi : P.index x with
  | mk a bi =>
    rcases bi with ⟨b,i⟩
    cases a with
    | inl a =>
      change exteriorCellStep n w d ell hell word closed c hc f (P.index x) = _ at he
      rw [hxi] at he
      cases he
    | inr a =>
      change exteriorCellStep n w d ell hell word closed c hc f (P.index x) = _ at he
      rw [hxi] at he
      have hs : (⟨a,b,i⟩ : (walkTarget n w d c hc f).ExteriorSide ell hell word closed) = s := Sum.inr.inj he
      rw [← hs]
      rw [hxi] at hx
      change some b = _ at hx
      split_ifs at hx with hm
      · exact Option.some.inj hx

end HyperbolicObstruction.ConeSkeleton
end

end OAI
