import Mathlib
import OAI.Geometry.HyperbolicGroups.WordPictureFold
import OAI.Geometry.HyperbolicGroups.IndexedWordPicture
import OAI.Geometry.HyperbolicGroups.IndexedPictureFold

namespace OAI

noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V A : Type*} [AddCommGroup A]
  {R : Set (Word E)} {w : Word E}
  {B : PolygonTarget.Boundary C (E × Bool) V} {P : WordPicture R w}
namespace Indexing
variable (I : Indexing B P) (weight : C → A)

lemma of_eq {v : Word E} (hw : w = v) :
    ∃ Q : WordPicture R v, ∃ J : Indexing B Q, J.chain weight = I.chain weight := by
  subst v
  exact ⟨P,I,rfl⟩

lemma of_step {v : Word E} (h : FreeGroup.Red.Step w v) :
    ∃ Q : WordPicture R v, ∃ J : Indexing B Q, J.chain weight = I.chain weight := by
  cases h with
  | @not l r x b =>
    obtain ⟨ls,rs,he,hl,hrs⟩ := List.map_eq_append_iff.mp P.word
    obtain ⟨a,rs',hr,ha,hrs'⟩ := List.map_eq_cons_iff.mp hrs
    obtain ⟨b',rs'',hr',hb,hrs''⟩ := List.map_eq_cons_iff.mp hrs'
    have hout : P.outside = ls++a::b'::rs'' := by rw [he,hr,hr']
    have hc : P.label a = invLetter (P.label b') := by rw [ha,hb]; simp [invLetter]
    have hw : (ls++rs'').map P.label = l++r := by rw [List.map_append,hl,hrs'']
    obtain ⟨Q,J,hJ⟩ := (I.foldAt hout hc).of_eq weight hw
    exact ⟨Q,J,hJ.trans (I.fold_chain hout hc weight)⟩

lemma of_red {v : Word E} (h : FreeGroup.Red w v) :
    ∃ Q : WordPicture R v, ∃ J : Indexing B Q, J.chain weight = I.chain weight := by
  induction h with
  | refl => exact ⟨P,I,rfl⟩
  | tail h h' ih =>
    obtain ⟨Q,J,hJ⟩ := ih
    obtain ⟨S,K,hK⟩ := J.of_step weight h'
    exact ⟨S,K,hK.trans hJ⟩

end Indexing
end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
