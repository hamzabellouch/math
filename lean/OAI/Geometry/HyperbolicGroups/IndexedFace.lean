import Mathlib
import OAI.Geometry.HyperbolicGroups.DipoleSwitch

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable

variable {D S : Type*}

/-- An indexed cellular face map. Commutation records EACH indexed side (not
just its edge label); injectivity on a face rules out wrapping a cell twice. -/
structure IndexedFaceMap (f : Perm D) (t : Perm S) (j : D → S) : Prop where
  commute : ∀ x, j (f x) = t (j x)
  injective : ∀ {x y}, f.SameCycle x y → j x = j y → x = y

lemma semiconj_perm_pow {f : Perm D} {t : Perm S} {j : D → S}
    (h : ∀ x, j (f x) = t (j x)) (k : ℕ) (x : D) :
    j ((f ^ k) x) = (t ^ k) (j x) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ',mul_apply,h,ih,pow_succ',mul_apply]

lemma semiconj_perm_inv {f : Perm D} {t : Perm S} {j : D → S}
    (h : ∀ x, j (f x) = t (j x)) (x : D) :
    j (f⁻¹ x) = t⁻¹ (j x) := by
  apply t.injective
  simpa only [Perm.inv_def,apply_symm_apply] using (h (f⁻¹ x)).symm

lemma semiconj_perm_zpow {f : Perm D} {t : Perm S} {j : D → S}
    (h : ∀ x, j (f x) = t (j x)) (k : ℤ) (x : D) :
    j ((f ^ k) x) = (t ^ k) (j x) := by
  cases k with
  | ofNat k => simpa using semiconj_perm_pow h k x
  | negSucc k =>
    simpa only [zpow_negSucc,inv_pow] using
      semiconj_perm_pow (semiconj_perm_inv h) (k+1) x

lemma semiconj_perm_sameCycle {f : Perm D} {t : Perm S} {j : D → S}
    (h : ∀ x, j (f x) = t (j x)) {a b : D} (hab : f.SameCycle a b) :
    t.SameCycle (j a) (j b) := by
  obtain ⟨k,rfl⟩ := hab
  exact ⟨k,(semiconj_perm_zpow h k a).symm⟩

namespace IndexedFaceMap
variable {f : Perm D} {t : Perm S} {j : D → S} (h : IndexedFaceMap f t j)
include h

/-- Every indexed face maps ONTO its full target side cycle as well. -/
lemma orbit_surjective (a : D) {s : S} (hs : t.SameCycle (j a) s) :
    ∃ b, f.SameCycle a b ∧ j b = s := by
  obtain ⟨k,rfl⟩ := hs
  exact ⟨(f^k) a,SameCycle.rfl.zpow_right,semiconj_perm_zpow h.commute k a⟩

def orbitEquiv (a : D) : {x : D // f.SameCycle a x} ≃ {s : S // t.SameCycle (j a) s} :=
  Equiv.ofBijective (fun x => ⟨j x.val,semiconj_perm_sameCycle h.commute x.property⟩) (by
    constructor
    · intro x y he
      exact Subtype.ext (h.injective (x.property.symm.trans y.property) (congrArg Subtype.val he))
    · intro s
      obtain ⟨b,hb,he⟩ := h.orbit_surjective a s.property
      exact ⟨⟨b,hb⟩,Subtype.ext he⟩)

@[simp] lemma orbitEquiv_val (a : D) (x : {x : D // f.SameCycle a x}) :
    (h.orbitEquiv a x).val = j x.val := rfl

/-- Opposite target sides, including their INDEX, determine opposite complete
source face parametrizations. In particular, this derives cancellation data
from a cellular map rather than taking opposite copies as an extra normality
assumption. Target cycles of opposite orientations are disjoint. -/
theorem opposite_faces [DecidableEq D] [Fintype D]
    (r : Perm S) (hr : r * r = 1)
    (hrev : ∀ s, r (t s) = t⁻¹ (r s))
    (hdisj : ∀ s, ¬ t.SameCycle s (r s))
    (a b : D) (hab : j b = r (j a)) :
    ∃ q : Perm {x : D // f.SameCycle a x},
      ∃ v : {x : D // f.SameCycle a x} → D,
        PictureMap.OppositeFaces f q Subtype.val v ∧
        v ⟨a,SameCycle.rfl⟩ = b ∧ ∀ x, j (v x) = r (j x.val) := by
  classical
  let I := {x : D // f.SameCycle a x}
  let q : Perm I := f.subtypePerm (fun x => sameCycle_apply_right)
  have hr' (s : S) : r (r s) = s := congrArg (fun p : Perm S => p s) hr
  have hv (x : I) : ∃ y, f.SameCycle b y ∧ j y = r (j x.val) := by
    apply h.orbit_surjective b
    rw [hab]
    exact (semiconj_perm_sameCycle hrev
      (semiconj_perm_sameCycle h.commute x.property)).of_inv
  let v : I → D := fun x => (hv x).choose
  have v_cycle (x : I) : f.SameCycle b (v x) := (hv x).choose_spec.1
  have v_map (x : I) : j (v x) = r (j x.val) := (hv x).choose_spec.2
  have v_inj : Function.Injective v := by
    intro x y he
    apply Subtype.ext
    apply h.injective (x.property.symm.trans y.property)
    apply r.injective
    rw [← v_map,← v_map,he]
  have v_disj (x y : I) : x.val ≠ v y := by
    intro he
    have hc : f.SameCycle a b := x.property.trans (he ▸ (v_cycle y).symm)
    have ht := semiconj_perm_sameCycle h.commute hc
    rw [hab] at ht
    exact hdisj (j a) ht
  have v_face (x : I) : f (v (q x)) = v x := by
    apply h.injective ((v_cycle (q x)).apply_right.symm.trans (v_cycle x))
    rw [h.commute,v_map,v_map]
    change t (r (j (f x.val))) = r (j x.val)
    rw [h.commute,hrev,Perm.inv_def,apply_symm_apply]
  refine ⟨q,v,⟨Subtype.val_injective,v_inj,v_disj,fun _ => rfl,v_face,?_⟩,?_,v_map⟩
  · intro x y
    exact (sameCycle_subtypePerm).mpr (x.property.symm.trans y.property)
  · apply h.injective (v_cycle ⟨a,SameCycle.rfl⟩).symm
    exact (v_map ⟨a,SameCycle.rfl⟩).trans hab.symm

end IndexedFaceMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
