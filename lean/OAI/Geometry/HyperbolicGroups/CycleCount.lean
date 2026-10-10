import Mathlib
import OAI.Geometry.HyperbolicGroups.PermSwitch

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
variable {D : Type*} [DecidableEq D] [Fintype D]

abbrev VertexClasses (p : Perm D) := Quotient (SameCycle.setoid p)
abbrev Classifier (p : Perm D) := Function.fixedPoints p ⊕ p.cycleFactorsFinset

def classify (p : Perm D) (d : D) : Classifier p :=
  if h : p d = d then .inl ⟨d,h⟩ else
    .inr ⟨p.cycleOf d,cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr h)⟩

lemma classify_eq_iff (p : Perm D) (a b : D) :
    classify p a = classify p b ↔ p.SameCycle a b := by
  by_cases ha : p a = a
  · constructor
    · intro he
      by_cases hb : p b = b
      · simp only [classify,dite_eq_left ha,dite_eq_left hb,Sum.inl.injEq] at he
        exact (congrArg Subtype.val he).sameCycle p
      · simp only [classify,dite_eq_left ha,dite_eq_right hb,Sum.inl_ne_inr] at he
    · intro he
      have hab := he.eq_of_left ha
      rw [hab]
  · constructor
    · intro he
      by_cases hb : p b = b
      · simp only [classify,dite_eq_right ha,dite_eq_left hb,Sum.inr_ne_inl] at he
      · simp only [classify,dite_eq_right ha,dite_eq_right hb,Sum.inr.injEq,Subtype.mk.injEq] at he
        exact (sameCycle_iff_cycleOf_eq_of_mem_support (mem_support.mpr ha) (mem_support.mpr hb)).mpr he
    · intro he
      have hb : p b ≠ b := fun hb => ha (he.apply_eq_self_iff.mpr hb)
      simp only [classify,dite_eq_right ha,dite_eq_right hb,Sum.inr.injEq,Subtype.mk.injEq]
      exact he.cycleOf_eq

def classifierMap (p : Perm D) : VertexClasses p → Classifier p :=
  Quotient.lift (classify p) (fun a b h => (classify_eq_iff p a b).mpr h)

lemma classifierMap_bijective (p : Perm D) : Function.Bijective (classifierMap p) := by
  constructor
  · intro a b
    induction a,b using Quotient.inductionOn₂ with
    | h a b =>
      intro he
      exact Quotient.sound ((classify_eq_iff p a b).mp he)
  · intro z
    cases z with
    | inl x =>
      refine ⟨Quotient.mk _ x.val,?_⟩
      change classify p x.val = Sum.inl x
      have hx : p x.val = x.val := x.property
      simp only [classify,dite_eq_left hx]
    | inr c =>
      obtain ⟨x,hx⟩ := (mem_cycleFactorsFinset_iff.mp c.property).1.nonempty_support
      have hp : p x ≠ x := mem_support.mp ((mem_cycleFactorsFinset_support_le c.property) hx)
      refine ⟨Quotient.mk _ x,?_⟩
      change classify p x = Sum.inr c
      simp only [classify,dite_eq_right hp,Sum.inr.injEq]
      apply Subtype.ext
      exact ((eq_cycleOf_of_mem_cycleFactorsFinset_iff p c c.property x).mpr hx).symm

/-- The numerical cycle count used in the Euler computation equals the actual
finite quotient of side corners by vertex-link connectivity. -/
theorem cycles_eq_card_classes (p : Perm D) :
    cycles p = Nat.card (VertexClasses p) := by
  classical
  let := Fintype.ofFinite (VertexClasses p)
  rw [Nat.card_eq_fintype_card]
  have hc := Fintype.card_congr (Equiv.ofBijective (classifierMap p) (classifierMap_bijective p))
  rw [hc,Fintype.card_sum,Fintype.card_coe,cycles_eq_fixed_add]
  simp [cycleType]

end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
