import Mathlib
import OAI.Geometry.HyperbolicGroups.WordPictureAppend
import OAI.Geometry.HyperbolicGroups.IndexedWordPicture

namespace OAI

noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V : Type*} {R : Set (Word E)} {u v : Word E}
  {B : PolygonTarget.Boundary C (E × Bool) V}
  {P : WordPicture R u} {Q : WordPicture R v}
namespace Indexing
variable (I : Indexing B P) (J : Indexing B Q)
  (hp : P.outside ≠ []) (hq : Q.outside ≠ [])

lemma append_left_boundary {x : P.Dart} (hx : x ∉ P.outside) :
    ∃ xs : List P.Dart, IsBoundary P.pairing.face xs ∧ x ∈ xs ∧
      IsBoundary (P.appendNonempty Q hp hq).pairing.face (xs.map Sum.inl) := by
  obtain ⟨xs,hs,hxm,_⟩ := P.interior x hx
  have hdis : ∀ a ∈ xs, a ∉ P.outside := by
    intro a ha hoa
    exact hx (P.boundary.mem_of_sameCycle hoa (hs.sameCycle ha hxm))
  refine ⟨xs,hs,hxm,?_⟩
  exact (hs.map (Sum.inl (β := Q.Dart)) Sum.inl_injective (fun _ => rfl)).splice_away
    (by simp only [List.mem_map]; rintro ⟨y,hy,he⟩
        exact hdis y hy (Sum.inl.inj he ▸ List.getLast_mem hp))
    (by simp)

lemma append_right_boundary {x : Q.Dart} (hx : x ∉ Q.outside) :
    ∃ xs : List Q.Dart, IsBoundary Q.pairing.face xs ∧ x ∈ xs ∧
      IsBoundary (P.appendNonempty Q hp hq).pairing.face (xs.map Sum.inr) := by
  obtain ⟨xs,hs,hxm,_⟩ := Q.interior x hx
  have hdis : ∀ a ∈ xs, a ∉ Q.outside := by
    intro a ha hoa
    exact hx (Q.boundary.mem_of_sameCycle hoa (hs.sameCycle ha hxm))
  refine ⟨xs,hs,hxm,?_⟩
  exact (hs.map (Sum.inr (α := P.Dart)) Sum.inr_injective (fun _ => rfl)).splice_away
    (by simp)
    (by simp only [List.mem_map]; rintro ⟨y,hy,he⟩
        exact hdis y hy (Sum.inr.inj he ▸ List.getLast_mem hq))

def appendNonempty : Indexing B (P.appendNonempty Q hp hq) where
  index := Sum.elim I.index J.index
  outside x := by
    change P.Dart ⊕ Q.Dart at x
    change Sum.elim I.index J.index x = none ↔
      x ∈ P.outside.map Sum.inl ++ Q.outside.map Sum.inr
    have hmem {α β : Type} (xs : List α) (ys : List β) (z : α ⊕ β) :
        Sum.elim (fun x => x ∈ xs) (fun y => y ∈ ys) z ↔
          z ∈ xs.map Sum.inl ++ ys.map Sum.inr := by
      cases z <;> simp
    cases x with
    | inl x => exact (I.outside x).trans (hmem P.outside Q.outside (.inl x))
    | inr x => exact (J.outside x).trans (hmem P.outside Q.outside (.inr x))
  commute x := by
    change P.Dart ⊕ Q.Dart at x
    let j := Sum.elim I.index J.index
    let a : P.Dart ⊕ Q.Dart := .inl (P.outside.getLast hp)
    let b : P.Dart ⊕ Q.Dart := .inr (Q.outside.getLast hq)
    have ha : j a = none := (I.outside _).mpr (List.getLast_mem hp)
    have hb : j b = none := (J.outside _).mpr (List.getLast_mem hq)
    have hs : j (swap a b x) = j x := by
      by_cases hxa : x = a
      · subst x; rw [swap_apply_left,ha,hb]
      by_cases hxb : x = b
      · subst x; rw [swap_apply_right,ha,hb]
      rw [swap_apply_of_ne_of_ne hxa hxb]
    have hc : ∀ z, j ((P.pairing.sum Q.pairing).face z) = (j z).map B.next := by
      intro z; cases z with
      | inl z => exact I.commute z
      | inr z => exact J.commute z
    exact (hc (swap a b x)).trans (congrArg (Option.map B.next) hs)
  injective := by
    intro x y hxy s hx hy
    change P.Dart ⊕ Q.Dart at x y
    cases x with
    | inl x =>
      have hxo : x ∉ P.outside := by
        intro h; have hh : some s = none := hx.symm.trans ((I.outside x).mpr h); cases hh
      obtain ⟨xs,hs,hxm,hms⟩ := append_left_boundary hp hq hxo
      obtain ⟨y',hy',he⟩ := List.mem_map.mp
        (hms.mem_of_sameCycle (List.mem_map.mpr ⟨x,hxm,rfl⟩) hxy)
      subst y
      exact congrArg Sum.inl (I.injective (hs.sameCycle hxm hy') s hx hy)
    | inr x =>
      have hxo : x ∉ Q.outside := by
        intro h; have hh : some s = none := hx.symm.trans ((J.outside x).mpr h); cases hh
      obtain ⟨xs,hs,hxm,hms⟩ := append_right_boundary hp hq hxo
      obtain ⟨y',hy',he⟩ := List.mem_map.mp
        (hms.mem_of_sameCycle (List.mem_map.mpr ⟨x,hxm,rfl⟩) hxy)
      subst y
      exact congrArg Sum.inr (J.injective (hs.sameCycle hxm hy') s hx hy)
  label x s hx := by
    cases x with
    | inl x => exact I.label x s hx
    | inr x => exact J.label x s hx

variable {A : Type*} [AddCommGroup A]
lemma append_chain (weight : C → A) :
    (I.appendNonempty J hp hq).chain weight = I.chain weight + J.chain weight := by
  change (∑ x : P.Dart ⊕ Q.Dart, cornerWeight weight (Sum.elim I.index J.index x)) = _
  rw [Fintype.sum_sum_type]
  rfl

end Indexing
end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
