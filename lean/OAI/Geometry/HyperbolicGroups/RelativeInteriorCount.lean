import Mathlib
import OAI.Geometry.HyperbolicGroups.RelativePartitionEstimate

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))
variable (xs : List P.Dart) (hx : IsBoundary P.pairing.face xs)
  (hw : xs.map ((target n w d ell hell word c hc f).label ∘ P.index) =
    List.ofFn (letterDart n w ∘ word))
  (ht : ∀ x, (walkTarget n w d c hc f).isExterior ell hell (letterDart n w ∘ word)
    (letterWordClosed n w ell word) (P.index x) ↔ x ∈ xs)

include hw in
lemma exterior_length : xs.length = ell := by
  simpa only [List.length_map,List.length_ofFn] using congrArg List.length hw

include ht in
lemma interior_mem (x : P.Dart) : Interior n w d ell hell word c hc f P (P.faceClass x) ↔ x ∉ xs := by
  rw [interior_iff,ht]

include hx hw ht in
lemma exterior_face_unique : ∃! F : P.Face, ¬ Interior n w d ell hell word c hc f P F := by
  have hl := exterior_length n w d ell hell word c hc f P xs hw
  have hn : xs ≠ [] := by intro he; simp [he] at hl; omega
  obtain ⟨x,hxm⟩ := List.exists_mem_of_ne_nil xs hn
  refine ⟨P.faceClass x,?_,?_⟩
  · change ¬ Interior n w d ell hell word c hc f P (P.faceClass x)
    exact fun hi => (interior_mem n w d ell hell word c hc f P xs ht x).mp hi hxm
  · intro F hF
    have hF' : ¬ Interior n w d ell hell word c hc f P (P.faceClass F.out) := by
      rwa [P.faceClass_out]
    rw [interior_mem n w d ell hell word c hc f P xs ht] at hF'
    have hFm := Classical.not_not.mp hF'
    rw [← P.faceClass_out F,P.faceClass_eq]
    exact hx.sameCycle hFm hxm

include hx hw ht in
/-- Exactly one face is exterior, even with free outside-to-outside folds. -/
lemma interior_card : (Fintype.card (InteriorFace n w d ell hell word c hc f P) : ℤ) =
    cycles P.pairing.face - 1 := by
  obtain ⟨F,hF,huniq⟩ := exterior_face_unique n w d ell hell word c hc f P xs hx hw ht
  have he : Fintype.card {G : P.Face // ¬ Interior n w d ell hell word c hc f P G} = 1 := by
    have : Unique {G : P.Face // ¬ Interior n w d ell hell word c hc f P G} := {
      default := ⟨F,hF⟩
      uniq := fun G => Subtype.ext (huniq G.val G.property) }
    exact Fintype.card_unique
  have hsum := Fintype.card_subtype_compl (Interior n w d ell hell word c hc f P)
  rw [he] at hsum
  rw [cycles_eq_card_classes]
  change (Fintype.card (InteriorFace n w d ell hell word c hc f P) : ℤ) = (Nat.card P.Face : ℤ) - 1
  rw [Nat.card_eq_fintype_card]
  have hle := Fintype.card_subtype_le (Interior n w d ell hell word c hc f P)
  simp only [← Nat.card_eq_fintype_card] at hsum hle
  have hh : Fintype.card (InteriorFace n w d ell hell word c hc f P) + 1 = Fintype.card P.Face := by
    simp only [← Nat.card_eq_fintype_card]
    change Nat.card {G : P.Face // Interior n w d ell hell word c hc f P G} + 1 = Nat.card P.Face
    omega
  have hh' : (Fintype.card (InteriorFace n w d ell hell word c hc f P) : ℤ) + 1 = Fintype.card P.Face := by exact_mod_cast hh
  omega

include hw ht in
lemma outside_contacts_le :
    Fintype.card (OutsideContact P.pairing (Interior n w d ell hell word c hc f P ∘ P.faceClass)) ≤ ell := by
  exact (outside_contacts_le_length P.pairing _ xs (interior_mem n w d ell hell word c hc f P xs ht)).trans_eq
    (exterior_length n w d ell hell word c hc f P xs hw)

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
