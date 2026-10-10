import Mathlib
import OAI.Geometry.HyperbolicGroups.FaceChainSelection
import OAI.Geometry.HyperbolicGroups.IndexedWordPicture

namespace OAI

noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V : Type*} {R : Set (Word E)}
  {B : PolygonTarget.Boundary C (E × Bool) V} {P : WordPicture R []}
namespace Indexing
variable (I : Indexing B P)

lemma closed_index_exists (x : P.Dart) : ∃ s, I.index x = some s := by
  have hout : P.outside = [] := List.map_eq_nil_iff.mp P.word
  cases hx : I.index x with
  | none => have hh := (I.outside x).mp hx; simp [hout] at hh
  | some s => exact ⟨s,rfl⟩

def closedIndex (x : P.Dart) : B.Side := (I.closed_index_exists x).choose
lemma closedIndex_spec (x : P.Dart) : I.index x = some (I.closedIndex x) :=
  (I.closed_index_exists x).choose_spec

lemma closed_mapped : IndexedFaceMap P.pairing.face B.next I.closedIndex := by
  constructor
  · intro x
    apply Option.some.inj
    rw [← I.closedIndex_spec, I.commute,I.closedIndex_spec]
    rfl
  · intro x y hxy he
    exact I.injective hxy (I.closedIndex x) (I.closedIndex_spec x)
      ((I.closedIndex_spec y).trans (congrArg some he.symm))

variable {A : Type*} [AddCommGroup A]
  (hrev : B.rev = invLetter) (weight : C → A)

def closedPicture : CellPicture (B.target weight (fun _ => false) (by intro _ impossible; cases impossible)) where
  Dart := P.Dart
  pairing := P.pairing
  genusZero := P.genusZero
  index := I.closedIndex
  mapped := I.closed_mapped
  respects := (B.target weight (fun _ => false) (by intro _ impossible; cases impossible)).respects_of_edge
    P.pairing I.closedIndex I.closed_mapped (by
      intro x
      change B.sideLabel (I.closedIndex (P.pairing.edge x)) = B.rev (B.sideLabel (I.closedIndex x))
      rw [← I.label _ _ (I.closedIndex_spec _),← I.label _ _ (I.closedIndex_spec _),hrev]
      exact P.paired x)

lemma closed_chain : (I.closedPicture hrev weight).chain = I.chain weight := by
  let T := B.target weight (fun _ => false) (by intro _ impossible; cases impossible)
  have hh := faceChain_eq_ite P.pairing.face (B.weight weight ∘ I.closedIndex)
    (fun x => by rw [Function.comp_apply,I.closed_mapped.commute]; rfl)
    (fun x => (I.closedIndex x).2.2 = (⟨0,B.positive (I.closedIndex x).1⟩ : Fin _))
    (I.closed_mapped.selected _ _ _ _ (B.marked_unique (fun c => ⟨0,B.positive c⟩)))
  change faceChain P.pairing.face (B.weight weight ∘ I.closedIndex) _ = _
  rw [hh]
  apply Finset.sum_congr rfl
  intro x _
  rw [I.closedIndex_spec]
  simp only [cornerWeight,Function.comp_apply,Fin.ext_iff]

end Indexing
end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
