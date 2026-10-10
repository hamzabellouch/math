import Mathlib
import OAI.Geometry.HyperbolicGroups.WordPicture
import OAI.Geometry.HyperbolicGroups.PictureMapFurther
import OAI.Geometry.HyperbolicGroups.BoundaryEraseList
import OAI.Geometry.HyperbolicGroups.OneFaceFilling

namespace OAI

noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {A : Type*} {R : Set (Word A)} {w : Word A}
variable (P : WordPicture R w)

/-- Components with no relator face are trees in genus zero even when the
whole picture has unrelated closed components. -/
theorem isolated_outside_filling
    (hclosed : ∀ x ∈ P.outside, P.pairing.edge x ∈ P.outside) :
    Homotopy R w [] 0 := by
  let p : P.Dart → Prop := fun x => x ∈ P.outside
  have hf : ∀ x, p (P.pairing.face x) ↔ p x := by
    intro x
    constructor
    · intro hx
      exact P.boundary.mem_of_sameCycle hx (SameCycle.rfl.apply_right.symm)
    · exact P.boundary.invariant
  have he : ∀ x, p (P.pairing.edge x) ↔ p x := by
    intro x
    constructor
    · intro hx
      simpa only [P.pairing.edge_edge] using hclosed _ hx
    · exact hclosed x
  let Q : WordPicture R w := {
    Dart := {x // p x}
    finite := @Subtype.fintype P.Dart p (fun x => Classical.propDecidable (p x)) P.finite
    pairing := P.pairing.restrict p hf he
    genusZero := P.pairing.restrict_genusZero p P.genusZero hf he
    label := fun x => P.label x.val
    paired := fun x => P.paired x.val
    outside := P.outside.attachWith p (fun _ hx => hx)
    boundary := P.boundary.lift (fun _ hx => hx) _ (fun _ _ => rfl)
    word := by
      rw [List.attachWith_map_val]
      exact P.word
    interior := fun x hx => False.elim (hx ((List.mem_attachWith _ x).mpr x.property)) }
  apply Q.one_face_filling
  intro x
  change x ∈ P.outside.attachWith p (fun _ hx => hx)
  exact (List.mem_attachWith _ x).mpr x.property

end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
