import Mathlib
import OAI.Geometry.HyperbolicGroups.WordPictureLiteral
import OAI.Geometry.HyperbolicGroups.PolygonBoundaryList
import OAI.Geometry.HyperbolicGroups.WordPictureMarked

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PolygonTarget.Boundary
open HyperbolicObstruction.PictureSwitch HyperbolicObstruction.WordPictures Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C A V M : Type*} [AddCommGroup M]
variable (B : PolygonTarget.Boundary C (A × Bool) V)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → A × Bool)
  (closed : ∀ i, B.start (word (finRotate ell i)) = B.start (B.rev (word i)))
variable (weight : C → M) (apex : V → Bool)
  (radial : ∀ l, apex (B.start l) = true → apex (B.start (B.rev l)) = false)

abbrev outsideTarget := (B.withOutside ell hell word closed).target
  (Sum.elim weight (fun _ => 0)) apex radial

/-- Every nonempty literal null word produces an actual mapped genus-zero
cell picture with ONE distinguished exterior boundary. Every other face maps
with its own indexed enumeration to a genuine attaching polygon, in either
orientation. The exterior has positive orientation and coefficient zero. -/
theorem nullWord_picture (hinv : B.rev = invLetter)
    (h : PresentedGroup.mk (FreeGroup.mk '' Set.range B.attachingWord)
      (FreeGroup.mk (List.ofFn word)) = 1) :
    ∃ (Q : CellPicture.{0} (B.outsideTarget ell hell word closed weight apex radial))
      (xs : List Q.Dart), IsBoundary Q.pairing.face xs ∧
      xs.map ((B.outsideTarget ell hell word closed weight apex radial).edge ∘ Q.index) = List.ofFn word ∧
      ∀ x, B.outsideTag ell hell word closed (Q.index x) =
        if x ∈ xs then some true else none := by
  let : DecidableEq (C ⊕ Unit) := Classical.decEq _
  let T := B.outsideTarget ell hell word closed weight apex radial
  have ht : T.rev = invLetter := hinv
  obtain ⟨P⟩ := literal_picture_existence (List.ofFn word) h
  have hR : ∀ r ∈ Set.range B.attachingWord,
      ∃ ys : List (B.withOutside ell hell word closed).Side,
        IsBoundary T.next ys ∧ ys.map T.edge = r ∧
        (∀ y ∈ ys, B.outsideTag ell hell word closed y = none ∧
          B.outsideTag ell hell word closed (T.opposite y) = none) := by
    rintro r ⟨c,rfl⟩
    refine ⟨(B.withOutside ell hell word closed).positiveSides (.inl c),
      (B.withOutside ell hell word closed).positiveSides_boundary _,?_,?_⟩
    · exact (B.withOutside ell hell word closed).positiveSides_label _
    · exact B.positive_inside_tag ell hell word closed c
  have hw : ∃ ys : List (B.withOutside ell hell word closed).Side,
      IsBoundary T.next ys ∧ ys.map T.edge = List.ofFn word ∧
      (∀ y ∈ ys, B.outsideTag ell hell word closed y = some true) := by
    refine ⟨(B.withOutside ell hell word closed).positiveSides (.inr ()),
      (B.withOutside ell hell word closed).positiveSides_boundary _,?_,?_⟩
    · exact (B.withOutside ell hell word closed).positiveSides_label _
    · exact B.positive_outside_tag ell hell word closed
  obtain ⟨j,hj,hl,hmark⟩ := P.cellular_index_tag T ht
    (B.outsideTag ell hell word closed) none (some true) hR hw
  let Q : CellPicture T := {
    Dart := P.Dart
    pairing := P.pairing
    index := j
    mapped := hj
    respects := T.respects_of_edge P.pairing j hj (by
      intro x
      rw [hl,hl,ht]
      exact P.paired x)
    genusZero := P.genusZero }
  refine ⟨Q,P.outside,P.boundary,?_,hmark⟩
  have he : T.edge ∘ j = P.label := funext hl
  exact (congrArg (List.map · P.outside) he).trans P.word

end HyperbolicObstruction.PictureSwitch.PolygonTarget.Boundary
end
end

section

end
end

end OAI
