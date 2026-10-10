import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureEuler
import OAI.Geometry.HyperbolicGroups.PictureMapFurther
import OAI.Geometry.HyperbolicGroups.IndexedFace
import OAI.Geometry.HyperbolicGroups.PolygonSphere

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D E : Type*} [DecidableEq D] [DecidableEq E] [Fintype D] [Fintype E]

lemma cycles_sum (p : Perm D) (q : Perm E) :
    cycles (Equiv.sumCongr p q) = cycles p + cycles q := by
  let j : D ⊕ E → Quotient (SameCycle.setoid p) ⊕ Quotient (SameCycle.setoid q) :=
    Sum.map (Quotient.mk _) (Quotient.mk _)
  have hc : ∀ x y, SameCycle (Equiv.sumCongr p q) x y ↔ j x = j y := by
    intro x y
    constructor
    · intro h
      apply sameCycle_one.mp (semiconj_perm_sameCycle (t := (1 : Perm (Quotient (SameCycle.setoid p) ⊕ Quotient (SameCycle.setoid q)))) (j := j) ?_ h)
      intro z; cases z with
      | inl z =>
        exact congrArg Sum.inl (Quotient.sound (SameCycle.rfl (f := p) (x := z)).apply_left)
      | inr z =>
        exact congrArg Sum.inr (Quotient.sound (SameCycle.rfl (f := q) (x := z)).apply_left)
    · cases x with
      | inl x => cases y with
        | inl y =>
          intro h
          exact semiconj_perm_sameCycle (f := p) (t := Equiv.sumCongr p q)
            (j := Sum.inl) (fun _ => rfl) (Quotient.exact (Sum.inl.inj h))
        | inr y =>
          intro h
          exact False.elim (Sum.inl_ne_inr (by exact h))
      | inr x => cases y with
        | inl y =>
          intro h
          exact False.elim (Sum.inr_ne_inl (by exact h))
        | inr y =>
          intro h
          exact semiconj_perm_sameCycle (f := q) (t := Equiv.sumCongr p q)
            (j := Sum.inr) (fun _ => rfl) (Quotient.exact (Sum.inr.inj h))
  have hj : Function.Surjective j := by
    intro z; cases z with
    | inl z => obtain ⟨x,rfl⟩ := Quotient.exists_rep z; exact ⟨Sum.inl x,rfl⟩
    | inr z => obtain ⟨x,rfl⟩ := Quotient.exists_rep z; exact ⟨Sum.inr x,rfl⟩
  rw [cycles_eq_card_classes,card_quotient_of_classifier _ j hc hj,Nat.card_sum,
    Nat.cast_add,← cycles_eq_card_classes,← cycles_eq_card_classes]

namespace PictureMap
variable (M : PictureMap D) (N : PictureMap E)

/-- Literal disjoint union of polygon side-pairings. -/
def sum : PictureMap (D ⊕ E) where
  face := Equiv.sumCongr M.face N.face
  edge := Equiv.sumCongr M.edge N.edge
  edge_sq := by
    apply Equiv.ext
    intro x; cases x <;> simp [M.edge_edge,N.edge_edge]
  edge_ne := by
    intro x h; cases x with
    | inl x => exact M.edge_ne x (Sum.inl.inj h)
    | inr x => exact N.edge_ne x (Sum.inr.inj h)

omit [DecidableEq D] [DecidableEq E] [Fintype D] [Fintype E] in
lemma sum_vertex : (M.sum N).vertex = Equiv.sumCongr M.vertex N.vertex := by
  apply Equiv.ext
  intro x; cases x <;> rfl

def sumClassifier : D ⊕ E → Quotient M.components ⊕ Quotient N.components :=
  Sum.map (Quotient.mk _) (Quotient.mk _)

omit [DecidableEq D] [DecidableEq E] in
lemma sum_components : ∀ x y, (M.sum N).components x y ↔ M.sumClassifier N x = M.sumClassifier N y := by
  have hleft : M.components ≤ ((M.sum N).components.comap Sum.inl) := by
    apply M.components_le
    · intro x
      exact (M.sum N).face_le_components (SameCycle.rfl (x := Sum.inl x)).apply_right
    · intro x
      exact (M.sum N).edge_le_components (SameCycle.rfl (x := Sum.inl x)).apply_right
  have hright : N.components ≤ ((M.sum N).components.comap Sum.inr) := by
    apply N.components_le
    · intro x
      exact (M.sum N).face_le_components (SameCycle.rfl (x := Sum.inr x)).apply_right
    · intro x
      exact (M.sum N).edge_le_components (SameCycle.rfl (x := Sum.inr x)).apply_right
  have hk : (M.sum N).components ≤ Setoid.ker (M.sumClassifier N) := by
    apply (M.sum N).components_le
    · intro x; cases x with
      | inl x => exact congrArg Sum.inl (Quotient.sound (M.face_le_components SameCycle.rfl.apply_right))
      | inr x => exact congrArg Sum.inr (Quotient.sound (N.face_le_components SameCycle.rfl.apply_right))
    · intro x; cases x with
      | inl x => exact congrArg Sum.inl (Quotient.sound (M.edge_le_components SameCycle.rfl.apply_right))
      | inr x => exact congrArg Sum.inr (Quotient.sound (N.edge_le_components SameCycle.rfl.apply_right))
  intro x y
  refine ⟨fun h => hk h,?_⟩
  cases x with
  | inl x => cases y with
    | inl y => intro h; exact hleft (Quotient.exact (Sum.inl.inj h))
    | inr y => intro h; exact False.elim (Sum.inl_ne_inr (by exact h))
  | inr x => cases y with
    | inl y => intro h; exact False.elim (Sum.inr_ne_inl (by exact h))
    | inr y => intro h; exact hright (Quotient.exact (Sum.inr.inj h))

omit [DecidableEq D] [DecidableEq E] in
lemma sum_components_card : Nat.card (Quotient (M.sum N).components) =
    Nat.card (Quotient M.components) + Nat.card (Quotient N.components) := by
  rw [card_quotient_of_classifier _ (M.sumClassifier N) (M.sum_components N) ?_,Nat.card_sum]
  intro z; cases z with
  | inl z => obtain ⟨x,rfl⟩ := Quotient.exists_rep z; exact ⟨Sum.inl x,rfl⟩
  | inr z => obtain ⟨x,rfl⟩ := Quotient.exists_rep z; exact ⟨Sum.inr x,rfl⟩

omit [DecidableEq D] [DecidableEq E] in
lemma sum_not_components (x : D) (y : E) : ¬ (M.sum N).components (Sum.inl x) (Sum.inr y) := by
  rw [M.sum_components N]
  exact Sum.inl_ne_inr

lemma sum_euler : (M.sum N).euler = M.euler + N.euler := by
  obtain ⟨n,hn⟩ := M.card_darts_even
  obtain ⟨m,hm⟩ := N.card_darts_even
  rw [euler,euler,euler,sum_vertex,cycles_sum]
  change cycles M.vertex + cycles N.vertex + cycles (Equiv.sumCongr M.face N.face) - _ = _
  rw [cycles_sum,Fintype.card_sum,Nat.cast_add]
  omega

theorem sum_genusZero (hM : M.GenusZero) (hN : N.GenusZero) : (M.sum N).GenusZero := by
  change (M.sum N).euler = _
  rw [M.sum_euler N,M.sum_components_card N]
  change M.euler = _ at hM
  change N.euler = _ at hN
  rw [hM,hN,Nat.cast_add,mul_add]

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
