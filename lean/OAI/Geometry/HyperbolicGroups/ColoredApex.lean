import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureMap
import OAI.Geometry.HyperbolicGroups.CycleCount
import OAI.Geometry.HyperbolicGroups.PermEuler

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

omit [DecidableEq D] [Fintype D] in
lemma sameCycle_subtypePerm_iff {P : D → Prop} (p : Perm D)
    (hp : ∀ x, P (p x) ↔ P x) (a b : Subtype P) :
    (p.subtypePerm hp).SameCycle a b ↔ p.SameCycle a.val b.val := by
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨n,?_⟩
    have h := congrArg Subtype.val hn
    simpa only [subtypePerm_zpow,subtypePerm_apply] using h
  · rintro ⟨n,hn⟩
    refine ⟨n,?_⟩
    apply Subtype.ext
    simpa only [subtypePerm_zpow,subtypePerm_apply] using hn

namespace PictureMap
variable (c : D → Bool) (M : PictureMap D)

def apexCount : ℕ := Nat.card (Quotient ((SameCycle.setoid M.vertex).comap
  (Subtype.val : {x : D // c x = true} → D)))

def apexPerm (h : ∀ x, c (M.vertex x) = c x) : Perm {x : D // c x = true} :=
  M.vertex.subtypePerm (fun x => by rw [h x])

lemma apexCount_eq (h : ∀ x, c (M.vertex x) = c x) :
    (M.apexCount c : ℤ) = cycles (M.apexPerm c h) := by
  rw [cycles_eq_card_classes]
  congr 1
  apply Nat.card_congr
  exact Quotient.congrRight (fun a b => (sameCycle_subtypePerm_iff M.vertex _ a b).symm)

omit [DecidableEq D] in
lemma color_of_sameCycle (h : ∀ x, c (M.vertex x) = c x) {a b : D}
    (hab : M.vertex.SameCycle a b) : c a = c b := by
  exact (sameCycle_le_of_apply (s := Setoid.ker c) (fun x => (h x).symm)) hab

omit [DecidableEq D] in
lemma radial_far {a b : D} (h : ∀ x, c (M.vertex x) = c x)
    (ha : c a = true) (hb : c (M.edge b) = false) :
    ¬ M.vertex.SameCycle a (M.edge b) := by
  intro he
  have hc := M.color_of_sameCycle c h he
  rw [ha,hb] at hc
  exact Bool.noConfusion hc

omit [Fintype D] in
lemma switch_color (h : ∀ x, c (M.vertex x) = c x) {a b : D}
    (hab : c a = c b) (hfar : c (M.edge a) = c (M.edge b)) :
    ∀ x, c ((M.switch a b).vertex x) = c x := by
  intro x
  rw [M.vertex_switch]
  simp only [mul_apply,h,Equiv.apply_swap_eq_self hfar,Equiv.apply_swap_eq_self hab]

omit [Fintype D] in
lemma apexPerm_switch (h : ∀ x, c (M.vertex x) = c x) {a b : D}
    (ha : c a = true) (hb : c b = true)
    (hfa : c (M.edge a) = false) (hfb : c (M.edge b) = false) :
    (M.switch a b).apexPerm c (M.switch_color c h (ha.trans hb.symm) (hfa.trans hfb.symm)) =
      M.apexPerm c h * swap (⟨a,ha⟩ : {x : D // c x = true}) ⟨b,hb⟩ := by
  ext x
  simp only [apexPerm,subtypePerm_apply,mul_apply]
  rw [M.vertex_switch]
  simp only [mul_apply]
  have hv : (swap (⟨a,ha⟩ : {x : D // c x = true}) ⟨b,hb⟩ x).val = swap a b x.val :=
    (Subtype.val_injective.swap_apply ⟨a,ha⟩ ⟨b,hb⟩ x).symm
  rw [hv]
  have hc : c (swap a b x.val) = true := by
    rw [Equiv.apply_swap_eq_self (ha.trans hb.symm)]
    exact x.property
  have hna : swap a b x.val ≠ M.edge a := by
    intro he; rw [he,hfa] at hc; exact Bool.noConfusion hc
  have hnb : swap a b x.val ≠ M.edge b := by
    intro he; rw [he,hfb] at hc; exact Bool.noConfusion hc
  rw [swap_apply_of_ne_of_ne hna hnb]

/-- The termination measure counts actual apex vertex instances, rather than
all vertices: at each repeated radial-label switch this increases by one. -/
theorem switch_apexCount (h : ∀ x, c (M.vertex x) = c x) {a b : D}
    (hne : a ≠ b) (hv : M.vertex.SameCycle a b)
    (ha : c a = true) (hb : c b = true)
    (hfa : c (M.edge a) = false) (hfb : c (M.edge b) = false) :
    (M.switch a b).apexCount c = M.apexCount c + 1 := by
  have hc : ∀ x, c ((M.switch a b).vertex x) = c x :=
    M.switch_color c h (ha.trans hb.symm) (hfa.trans hfb.symm)
  have hs : (M.apexPerm c h).SameCycle ⟨a,ha⟩ ⟨b,hb⟩ :=
    (sameCycle_subtypePerm_iff M.vertex _ _ _).mpr hv
  have hn : (⟨a,ha⟩ : {x : D // c x = true}) ≠ ⟨b,hb⟩ :=
    fun he => hne (congrArg Subtype.val he)
  have he := cycles_split_right (M.apexPerm c h) hn hs
  rw [← M.apexPerm_switch c h ha hb hfa hfb] at he
  rw [← (M.switch a b).apexCount_eq c hc,← M.apexCount_eq c h] at he
  omega

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
