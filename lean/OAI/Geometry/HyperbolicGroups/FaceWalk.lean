import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureMap
import OAI.Geometry.HyperbolicGroups.PermEuler
import OAI.Geometry.HyperbolicGroups.FaceSplit
import OAI.Geometry.HyperbolicGroups.MappedPicture

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D C V : Type*} [DecidableEq D] [Fintype D]
namespace PictureMap

/-- A literal closed target walk on each source face: the next side starts
where this side ends. This imposes no injectivity or normal form. -/
def FaceClosed (M : PictureMap D) (source target : D → V) : Prop :=
  ∀ x, source (M.face x) = target x

/-- The indexed target occurrence stays constant around each source face.
Distinct occurrence indices remain distinct even if their labels agree. -/
def FaceKind (M : PictureMap D) (kind : D → C) : Prop := ∀ x, kind (M.face x) = kind x

omit [DecidableEq D] in
lemma kind_cycle {M : PictureMap D} {kind : D → C} (hk : M.FaceKind kind)
    {a b : D} (h : M.face.SameCycle a b) : kind a = kind b := by
  exact (sameCycle_le_of_apply (s := Setoid.ker kind) (fun x => (hk x).symm)) h

omit [Fintype D] in
lemma splice_closed {M : PictureMap D} {source target : D → V}
    (hclosed : M.FaceClosed source target) {a b : D} (hab : target a = target b) :
    (M.splice a b).FaceClosed source target := by
  intro x
  change source (M.face (swap a b x)) = target x
  rw [hclosed,Equiv.apply_swap_eq_self hab]

omit [Fintype D] in
lemma splice_kind {M : PictureMap D} {kind : D → C} (hk : M.FaceKind kind)
    {a b : D} (hab : kind a = kind b) : (M.splice a b).FaceKind kind := by
  intro x
  change kind (M.face (swap a b x)) = kind x
  rw [hk,Equiv.apply_swap_eq_self hab]

/-- Split repeated vertex visits in selected kinds of closed polygon walks.
Only face permutations change; all oriented steps, occurrence indices, edge
pairings and therefore every additive cone-step chain are retained literally.
Unselected faces retain their entire cyclic parametrization. The normalization
is a finite maximization, not an assumed simple-polygon representative. -/
theorem normalize_simple_faces (M : PictureMap D) (hG : M.GenusZero)
    (source target : D → V) (hc : M.FaceClosed source target)
    (kind : D → C) (hk : M.FaceKind kind) (free : C → Bool) :
    ∃ N : PictureMap D,
      N.edge = M.edge ∧ N.GenusZero ∧ N.FaceClosed source target ∧ N.FaceKind kind ∧
      (∀ x, free (kind x) = false → N.face x = M.face x) ∧
      ∀ a b, free (kind a) = true → N.face.SameCycle a b → target a = target b → a = b := by
  classical
  let good : PictureMap D → Prop := fun N =>
    N.edge = M.edge ∧ N.GenusZero ∧ N.FaceClosed source target ∧ N.FaceKind kind ∧
      ∀ x, free (kind x) = false → N.face x = M.face x
  let := Fintype.ofFinite (PictureMap D)
  let s := Finset.univ.filter good
  have hm : M ∈ s := by
    simp only [s,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨rfl,hG,hc,hk,fun _ _ => rfl⟩
  obtain ⟨N,hN,hmax⟩ := s.exists_max_image (fun N => cycles N.face) ⟨M,hm⟩
  have hn : good N := (Finset.mem_filter.mp hN).2
  refine ⟨N,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2,?_⟩
  intro a b ha hab ht
  by_contra hne
  have hk' : kind a = kind b := kind_cycle hn.2.2.2.1 hab
  have hsplit : good (N.splice a b) := by
    refine ⟨hn.1,N.split_genusZero hn.2.1 a b hne hab,
      splice_closed hn.2.2.1 ht,splice_kind hn.2.2.2.1 hk',?_⟩
    intro x hx
    have hxa : x ≠ a := by intro he; rw [he,ha] at hx; cases hx
    have hxb : x ≠ b := by intro he; rw [he,← hk',ha] at hx; cases hx
    change N.face (swap a b x) = M.face x
    rw [swap_apply_of_ne_of_ne hxa hxb]
    exact hn.2.2.2.2 x hx
  have hmem : N.splice a b ∈ s := by
    simp only [s,Finset.mem_filter,Finset.mem_univ,true_and]
    exact hsplit
  have hbound := hmax (N.splice a b) hmem
  have hinc := cycles_split_right N.face hne hab
  change cycles (N.face * swap a b) ≤ cycles N.face at hbound
  omega

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
