import Mathlib
import OAI.Geometry.HyperbolicGroups.BoundaryRotation
import OAI.Geometry.HyperbolicGroups.PictureLeaf

namespace OAI

noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {A : Type*} {R : Set (Word A)}

/-- Base case of planar extraction, proved from the combinatorial Euler
definition: a genus-zero picture with no interior darts has a zero-area
word filling. It is NOT postulated as a property of a picture. -/
theorem one_face_filling {w : Word A} (P : WordPicture R w) (hall : ∀ x, x ∈ P.outside) :
    Homotopy R w [] 0 := by
  by_cases he : P.outside = []
  · have hw : w = [] := by rw [← P.word,he]; rfl
    subst w
    exact .refl _
  obtain ⟨x,hx⟩ := P.pairing.single_face_leaf P.genusZero P.boundary hall he
  obtain ⟨i,hi,z,hz⟩ := P.boundary.adjacent_rotate (hall (P.pairing.edge x))
    (P.pairing.edge_ne x) hx
  let Q := P.rotate i
  have hq : Q.outside = []++P.pairing.edge x::x::z := hz
  have hc : Q.label (P.pairing.edge x) = invLetter (Q.label x) := P.paired x
  have H := one_face_filling (w := _) (Q.foldAt hq hc)
    (Q.all_outside_fold hq hc (P.all_outside_rotate hall i))
  have hword : w.rotate i = Q.label (P.pairing.edge x) :: Q.label x :: z.map Q.label :=
    Q.word.symm.trans (congrArg (List.map Q.label) hq)
  have hf : Homotopy R (w.rotate i) (z.map P.label) 0 := by
    rw [hword]
    apply Homotopy.free
    have hh : FreeGroup.mk [Q.label (P.pairing.edge x),Q.label x] = 1 := by
      rw [hc]
      change FreeGroup.mk (FreeGroup.invRev [Q.label x] ++ [Q.label x]) = 1
      rw [← FreeGroup.mul_mk,← FreeGroup.inv_mk,inv_mul_cancel]
    change FreeGroup.mk ([Q.label (P.pairing.edge x),Q.label x] ++ z.map Q.label) = _
    rw [← FreeGroup.mul_mk,hh,one_mul]
    rfl
  have hfill : Homotopy R (w.rotate i) [] 0 := by
    simpa only [List.nil_append,Nat.zero_add] using hf.trans H
  apply Homotopy.unrotate_null i _ hfill
  have heq : P.outside.length = w.length := by simpa using congrArg List.length P.word
  omega
termination_by Fintype.card P.Dart
decreasing_by
  have hc := card_offPair (P.pairing.edge_ne x)
  change Fintype.card {y : P.Dart // OffPair (P.pairing.edge x) x y} < Fintype.card P.Dart
  omega

end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
