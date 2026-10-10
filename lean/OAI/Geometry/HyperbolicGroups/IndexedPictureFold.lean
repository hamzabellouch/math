import Mathlib
import OAI.Geometry.HyperbolicGroups.StarMean
import OAI.Geometry.HyperbolicGroups.WordPictureFold
import OAI.Geometry.HyperbolicGroups.IndexedWordPicture

namespace OAI

noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V : Type*} {R : Set (Word E)} {w : Word E}
  {B : PolygonTarget.Boundary C (E × Bool) V} {P : WordPicture R w}
namespace Indexing
variable (I : Indexing B P) {l r : List P.Dart} {a b : P.Dart}
  (he : P.outside = l++a::b::r) (hc : P.label a = invLetter (P.label b))

lemma fold_outside (x : (P.foldAt he hc).Dart) :
    x.val ∈ P.outside ↔ x ∈ (P.foldAt he hc).outside := by
  change {x : P.Dart // OffPair a b x} at x
  change x.val ∈ P.outside ↔ x ∈ (l++r).attachWith (OffPair a b) _
  rw [List.mem_attachWith,he]
  simp only [List.mem_append,List.mem_cons,x.property.1,x.property.2,false_or]

def foldAt : Indexing B (P.foldAt he hc) where
  index x := I.index x.val
  outside x := (I.outside x.val).trans (fold_outside he hc x)
  commute x := by
    by_cases hxo : x.val ∈ P.outside
    · have hxo' := (fold_outside he hc x).mp hxo
      have hfo := (P.foldAt he hc).boundary.invariant hxo'
      have hh := (fold_outside he hc _).mpr hfo
      rw [(I.outside _).mpr hh,(I.outside _).mpr hxo]
      rfl
    · have hb : IsBoundary P.pairing.face (l++a::b::r) := he ▸ P.boundary
      have hab : a ≠ b := by
        have hn := (List.nodup_append.mp hb.nodup).2.1
        exact fun h => (List.nodup_cons.mp hn).1 (by simp [h])
      have hh := P.pairing.boundaryFold_other_face hab hb.middle_next x (by
        intro hh
        exact hxo (P.boundary.mem_of_sameCycle (by rw [he]; simp) hh))
      change I.index ((P.pairing.boundaryFold hab hb.middle_next).face x).val = _
      rw [hh]
      exact I.commute x.val
  injective hxy s hx hy := by
    have hb : IsBoundary P.pairing.face (l++a::b::r) := he ▸ P.boundary
    have hab : a ≠ b := by
      have hn := (List.nodup_append.mp hb.nodup).2.1
      exact fun h => (List.nodup_cons.mp hn).1 (by simp [h])
    apply Subtype.ext
    apply I.injective _ s hx hy
    exact (P.pairing.boundaryFold_face_orbits hab hb.middle_next _ _).mp hxy
  label x s hx := I.label x.val s hx

variable {A : Type*} [AddCommGroup A]
lemma fold_chain (weight : C → A) : (I.foldAt he hc).chain weight = I.chain weight := by
  have ha : I.index a = none := (I.outside a).mpr (by rw [he]; simp)
  have hb : I.index b = none := (I.outside b).mpr (by rw [he]; simp)
  change (∑ x : {x : P.Dart // OffPair a b x}, cornerWeight weight (I.index x.val)) = _
  erw [HyperbolicObstruction.sum_subtype_eq_ite (OffPair a b)
    (fun x : P.Dart => cornerWeight weight (I.index x))]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hxa : x = a
  · subst x; simp [OffPair,ha,cornerWeight]
  by_cases hxb : x = b
  · subst x; simp [OffPair,hb,cornerWeight]
  simp [OffPair,hxa,hxb]

end Indexing
end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
