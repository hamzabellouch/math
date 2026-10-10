import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureEuler

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

lemma sameCycle_after_swap_right (p : Perm D) {a b : D}
    (h : ¬ p.SameCycle a b) : (p * swap a b).SameCycle a b := by
  by_contra hn
  have h1 := cycles_merge_right p h
  have h2 := cycles_merge_right (p * swap a b) hn
  simp only [mul_assoc,swap_mul_self,mul_one] at h2
  omega

namespace PictureMap
variable (M : PictureMap D)

lemma components_le_glue_switch (a b : D) :
    M.components ≤ glue (M.switch a b).components a b := by
  let s := glue (M.switch a b).components a b
  have hs : (M.switch a b).components ≤ s := le_glue _ _ _
  have ht : ∀ x, s x (swap a b x) := fun x =>
    sameCycle_swap_le (glue_pair _ a b) SameCycle.rfl.apply_right
  apply M.components_le
  · intro x
    exact hs ((M.switch a b).face_le_components SameCycle.rfl.apply_right)
  · intro x
    have hx := hs ((M.switch a b).edge_le_components (SameCycle.rfl (x := swap a b x)).apply_right)
    have hh := s.trans' (ht x) (s.trans' hx (ht ((M.switch a b).edge (swap a b x))))
    simpa only [switch,mul_apply,swap_apply_self] using hh

lemma switch_components_le_glue (a b : D) :
    (M.switch a b).components ≤ glue M.components a b := by
  let s := glue M.components a b
  have hs : M.components ≤ s := le_glue _ _ _
  have ht : ∀ x, s x (swap a b x) := fun x =>
    sameCycle_swap_le (glue_pair _ a b) SameCycle.rfl.apply_right
  apply (M.switch a b).components_le
  · intro x
    exact hs (M.face_le_components SameCycle.rfl.apply_right)
  · intro x
    have hx := hs (M.edge_le_components (SameCycle.rfl (x := swap a b x)).apply_right)
    exact s.trans' (ht x) (s.trans' hx (ht (M.edge (swap a b x))))

/-- Restoring a single connection between the two new apex instances recovers
exactly the previous surface components. In particular a switch can split
only the affected component, into at most two components. -/
theorem switch_components_glue (a b : D) (hv : M.vertex.SameCycle a b) :
    glue (M.switch a b).components a b = M.components := by
  have hab : M.components a b := M.vertex_le_components hv
  have hnew : (M.switch a b).components ≤ M.components := by
    have h := M.switch_components_le_glue a b
    rwa [glue_eq_of_rel _ _ _ hab] at h
  exact le_antisymm (glue_le _ _ _ hnew hab) (M.components_le_glue_switch a b)

theorem switch_components_card (a b : D) (hv : M.vertex.SameCycle a b) :
    (Nat.card (Quotient (M.switch a b).components) : ℤ) =
      Nat.card (Quotient M.components) +
        if (M.switch a b).components a b then 0 else 1 := by
  have h := card_glue (M.switch a b).components a b
  rw [M.switch_components_glue a b hv] at h
  omega

omit [Fintype D] in
lemma switch_edge_a (a b : D)
    (hfar : ¬ M.vertex.SameCycle a (M.edge b)) :
    (M.switch a b).edge a = M.edge b := by
  have ha : M.edge b ≠ a := fun he => hfar (he.symm.sameCycle M.vertex)
  simp only [switch,mul_apply,swap_apply_left,
    swap_apply_of_ne_of_ne ha (M.edge_ne b)]

omit [Fintype D] in
lemma switch_edge_b (a b : D) (hv : M.vertex.SameCycle a b)
    (hfar : ¬ M.vertex.SameCycle a (M.edge a)) :
    (M.switch a b).edge b = M.edge a := by
  have hb : M.edge a ≠ b := fun he => hfar (he.symm ▸ hv)
  simp only [switch,mul_apply,swap_apply_right,
    swap_apply_of_ne_of_ne (M.edge_ne a) hb]

/-- When the far vertices were distinct, their merged link still joins both
switched edges. Thus no component is split in this case. -/
theorem switch_components_eq_of_far_distinct (a b : D)
    (hv : M.vertex.SameCycle a b)
    (hfar₁ : ¬ M.vertex.SameCycle a (M.edge a))
    (hfar₂ : ¬ M.vertex.SameCycle a (M.edge b))
    (hne : ¬ M.vertex.SameCycle (M.edge a) (M.edge b)) :
    (M.switch a b).components = M.components := by
  let q := M.vertex * swap (M.edge a) (M.edge b)
  have hq : q.SameCycle (M.edge a) (M.edge b) := sameCycle_after_swap_right _ hne
  have hqab : q.SameCycle a b := (sameCycle_right_swap_away _ hfar₁ hfar₂).mpr hv
  have hqa : ¬ q.SameCycle (M.edge a) a := fun h =>
    hfar₁ ((sameCycle_right_swap_away _ hfar₁ hfar₂).mp h.symm)
  have hqb : ¬ q.SameCycle (M.edge a) b := fun h => hqa (h.trans hqab.symm)
  have hnew : (M.switch a b).vertex.SameCycle (M.edge a) (M.edge b) := by
    rw [M.vertex_switch]
    exact (sameCycle_right_swap_away q hqa hqb).mpr hq
  have ha : (M.switch a b).components a (M.edge b) := by
    rw [← M.switch_edge_a a b hfar₂]
    exact (M.switch a b).edge_le_components SameCycle.rfl.apply_right
  have hb : (M.switch a b).components b (M.edge a) := by
    rw [← M.switch_edge_b a b hv hfar₁]
    exact (M.switch a b).edge_le_components SameCycle.rfl.apply_right
  have hab : (M.switch a b).components a b :=
    (M.switch a b).components.trans' ha
      ((M.switch a b).components.trans' ((M.switch a b).vertex_le_components hnew.symm)
        ((M.switch a b).components.symm' hb))
  have h := M.switch_components_glue a b hv
  rwa [glue_eq_of_rel _ _ _ hab] at h

/-- Genus-zero preservation under radial-label normalization.
Counts refer to actual permutation cycles and their actual
component quotient; Euler's bound was proved without surface classification. -/
theorem switch_genusZero (hM : M.GenusZero) (a b : D) (hab : a ≠ b)
    (hv : M.vertex.SameCycle a b)
    (hfar₁ : ¬ M.vertex.SameCycle a (M.edge a))
    (hfar₂ : ¬ M.vertex.SameCycle a (M.edge b)) : (M.switch a b).GenusZero := by
  have hE := M.switch_euler a b hab hv hfar₁ hfar₂
  change M.euler = _ at hM
  change (M.switch a b).euler = _
  by_cases hf : M.vertex.SameCycle (M.edge a) (M.edge b)
  · rw [ite_eq_left hf,hM] at hE
    have hC := M.switch_components_card a b hv
    have hbound := (M.switch a b).euler_le
    split_ifs at hC <;> omega
  · rw [ite_eq_right hf,hM] at hE
    rw [M.switch_components_eq_of_far_distinct a b hv hfar₁ hfar₂ hf]
    omega

/-- In the same-far-vertex case there are exactly TWO descendants of the old
component (globally, the component count increases by one). -/
theorem switch_card_of_far_same (hM : M.GenusZero) (a b : D) (hab : a ≠ b)
    (hv : M.vertex.SameCycle a b)
    (hfar₁ : ¬ M.vertex.SameCycle a (M.edge a))
    (hfar₂ : ¬ M.vertex.SameCycle a (M.edge b))
    (hf : M.vertex.SameCycle (M.edge a) (M.edge b)) :
    Nat.card (Quotient (M.switch a b).components) = Nat.card (Quotient M.components) + 1 := by
  have hG := M.switch_genusZero hM a b hab hv hfar₁ hfar₂
  have hE := M.switch_euler a b hab hv hfar₁ hfar₂
  rw [ite_eq_left hf] at hE
  change M.euler = _ at hM
  change (M.switch a b).euler = _ at hG
  omega

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
