import Mathlib
import OAI.Geometry.HyperbolicGroups.IndexedPictureAppend
import OAI.Geometry.HyperbolicGroups.IndexedPictureReduction

namespace OAI

/-! Disk-chain uniqueness follows from actual genus-zero sphere vanishing.
All operations retain the originally chosen precise interior cell identities. -/
noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture.Indexing
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V A : Type*} [AddCommGroup A]
  {R : Set (Word E)} {B : PolygonTarget.Boundary C (E × Bool) V}
  (hrev : B.rev = invLetter) (weight : C → A)
  (H : ∀ (S : WordPicture R []) (K : Indexing B S), K.chain weight = 0)

include hrev H in
lemma chain_unique {w : Word E} (P Q : WordPicture R w)
    (I : Indexing B P) (J : Indexing B Q) : I.chain weight = J.chain weight := by
  classical
  by_cases hw : w = []
  · subst w
    rw [H P I,H Q J]
  have hp : P.outside ≠ [] := by
    intro hp; apply hw; rw [← P.word,hp]; rfl
  have hq : Q.mirror.outside ≠ [] := by
    intro hq
    have hq' : Q.outside = [] := List.reverse_eq_nil_iff.mp hq
    apply hw; rw [← Q.word,hq']; rfl
  let K := I.appendNonempty (J.mirror hrev) hp hq
  have hred : FreeGroup.Red (w ++ FreeGroup.invRev w) [] := by
    have he : FreeGroup.reduce (w ++ FreeGroup.invRev w) = [] := by
      rw [← FreeGroup.toWord_mk,← FreeGroup.mul_mk,← FreeGroup.inv_mk,mul_inv_cancel,FreeGroup.toWord_one]
    simpa only [he] using (FreeGroup.reduce.red (L := w ++ FreeGroup.invRev w))
  obtain ⟨S,L,hL⟩ := K.of_red weight hred
  have hz := H S L
  rw [hL] at hz
  change (I.appendNonempty (J.mirror hrev) hp hq).chain weight = 0 at hz
  rw [append_chain,mirror_chain] at hz
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hz)

include hrev H in
lemma chain_free_eq {u v : Word E} (P : WordPicture R u) (Q : WordPicture R v)
    (I : Indexing B P) (J : Indexing B Q) (he : FreeGroup.mk u = FreeGroup.mk v) :
    I.chain weight = J.chain weight := by
  obtain ⟨w,hu,hv⟩ := FreeGroup.Red.exact.mp he
  obtain ⟨P',I',hI⟩ := I.of_red weight hu
  obtain ⟨Q',J',hJ⟩ := J.of_red weight hv
  exact hI.symm.trans ((chain_unique hrev weight H P' Q' I' J').trans hJ)

end HyperbolicObstruction.WordPictures.WordPicture.Indexing
end

end OAI
