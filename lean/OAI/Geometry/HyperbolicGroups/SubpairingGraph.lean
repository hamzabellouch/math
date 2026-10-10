import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureMap
import OAI.Geometry.HyperbolicGroups.PermEuler
import OAI.Geometry.HyperbolicGroups.PictureUnderlyingGraph

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

omit [Fintype D] in
lemma swaps_fix_of_outside (l : List (D × D)) (x : D)
    (h : ∀ ab ∈ l, x ≠ ab.1 ∧ x ≠ ab.2) : swaps l x = x := by
  induction l with
  | nil => rfl
  | cons ab l ih =>
    change swap ab.1 ab.2 (swaps l x) = x
    rw [ih (fun z hz => h z (List.mem_cons_of_mem _ hz))]
    exact swap_apply_of_ne_of_ne (h ab List.mem_cons_self).1
      (h ab List.mem_cons_self).2

namespace PictureMap
variable (M : PictureMap D) (q : Perm D) (hq : q*q = 1)

def subpairingGraph : SimpleGraph M.GraphVertex where
  Adj v w := v ≠ w ∧ ∃ x : D, M.vertexClass x = v ∧ M.vertexClass (q x) = w
  symm := ⟨by
    rintro v w ⟨hne,x,hx,he⟩
    refine ⟨hne.symm,q x,he,?_⟩
    have hh : q (q x) = x := congrArg (fun p : Perm D => p x) hq
    rw [hh]; exact hx⟩
  loopless := ⟨by rintro v ⟨h,_⟩; exact h rfl⟩

omit [DecidableEq D] in
lemma subpairing_reachable (x y : D)
    (h : (SameCycle.setoid M.vertex ⊔ SameCycle.setoid q) x y) :
    (M.subpairingGraph q hq).Reachable (M.vertexClass x) (M.vertexClass y) := by
  have hle : SameCycle.setoid M.vertex ⊔ SameCycle.setoid q ≤
      Setoid.comap M.vertexClass (M.subpairingGraph q hq).reachableSetoid := by
    apply sup_le
    · intro a b hab
      change (M.subpairingGraph q hq).Reachable (M.vertexClass a) (M.vertexClass b)
      rw [(M.vertexClass_eq_iff a b).mpr hab]
    · apply sameCycle_le_of_apply
      intro a
      change (M.subpairingGraph q hq).Reachable (M.vertexClass a) (M.vertexClass (q a))
      by_cases he : M.vertexClass a = M.vertexClass (q a)
      · rw [he]
      · exact SimpleGraph.Adj.reachable ⟨he,a,rfl,rfl⟩
  exact hle h

omit [DecidableEq D] in
lemma subpairing_connected [Nonempty D]
    (hspan : SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = ⊤) :
    (M.subpairingGraph q hq).Connected := by
  have : Nonempty M.GraphVertex := ⟨M.vertexClass (Classical.arbitrary D)⟩
  apply SimpleGraph.Connected.mk
  intro v w
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective v
  obtain ⟨y,rfl⟩ := Quotient.mk_surjective w
  apply M.subpairing_reachable q hq x y
  rw [hspan]; trivial

lemma subpairing_edge_card_le (l : List (D × D)) (hl : swaps l = q)
    (hpairs : ∀ ab ∈ l, q ab.1 = ab.2) :
    Nat.card (M.subpairingGraph q hq).edgeSet ≤ l.length := by
  classical
  let f : D × D → Sym2 M.GraphVertex := fun ab => s(M.vertexClass ab.1,M.vertexClass ab.2)
  have hsub : (M.subpairingGraph q hq).edgeFinset ⊆ l.toFinset.image f := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf v w =>
      have hadj : (M.subpairingGraph q hq).Adj v w := by simpa using he
      obtain ⟨hne,x,rfl,rfl⟩ := hadj
      have hqx : q x ≠ x := fun hh => hne (congrArg M.vertexClass hh.symm)
      have hex : ∃ ab ∈ l, x = ab.1 ∨ x = ab.2 := by
        by_contra h
        push Not at h
        exact hqx (hl ▸ swaps_fix_of_outside l x h)
      obtain ⟨ab,hab,ha | hb⟩ := hex
      · apply Finset.mem_image.mpr
        refine ⟨ab,List.mem_toFinset.mpr hab,?_⟩
        dsimp only [f]
        rw [ha,hpairs ab hab]
      · apply Finset.mem_image.mpr
        refine ⟨ab,List.mem_toFinset.mpr hab,?_⟩
        have hh : q ab.2 = ab.1 := by
          rw [← hpairs ab hab]
          exact congrArg (fun p : Perm D => p ab.1) hq
        dsimp only [f]
        rw [hb,hh,Sym2.eq_swap]
  calc
    Nat.card (M.subpairingGraph q hq).edgeSet = (M.subpairingGraph q hq).edgeFinset.card := by
      rw [Nat.card_eq_fintype_card,SimpleGraph.edgeFinset_card]
    _ ≤ (l.toFinset.image f).card := Finset.card_le_card hsub
    _ ≤ l.toFinset.card := Finset.card_image_le
    _ ≤ l.length := List.toFinset_card_le l

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
