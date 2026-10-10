import Mathlib
import OAI.Geometry.HyperbolicGroups.PermErase

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*}

def OffPair (a b x : D) : Prop := x ≠ a ∧ x ≠ b

lemma offPair_invariant {p : Perm D} {a b : D} (ha : p a = a) (hb : p b = b) (x : D) :
    OffPair a b (p x) ↔ OffPair a b x := by
  change (p x ≠ a ∧ p x ≠ b) ↔ (x ≠ a ∧ x ≠ b)
  have h₁ : p x = a ↔ x = a := by simpa only [ha] using (p.apply_eq_iff_eq (x := x) (y := a))
  have h₂ : p x = b ↔ x = b := by simpa only [hb] using (p.apply_eq_iff_eq (x := x) (y := b))
  simp only [ne_eq,h₁,h₂]

variable [DecidableEq D]

lemma bypass_keeps_fixed (p : Perm D) {a b : D} (hab : a ≠ b) (hb : p b = b) :
    bypass p a b = b := by
  rw [bypass_away p a b hab.symm,hb,ite_eq_right hab.symm]

def bypassPair (p : Perm D) (a b : D) : Perm D := bypass (bypass p a) b

lemma bypassPair_a (p : Perm D) {a b : D} (hab : a ≠ b) : bypassPair p a b a = a :=
  bypass_keeps_fixed (bypass p a) hab.symm (bypass_fixed p a)
lemma bypassPair_b (p : Perm D) (a b : D) : bypassPair p a b b = b := bypass_fixed _ _

def erasePair (p : Perm D) {a b : D} (hab : a ≠ b) : Perm {x // OffPair a b x} :=
  (bypassPair p a b).subtypePerm (offPair_invariant (bypassPair_a p hab) (bypassPair_b p a b))

variable [Fintype D]

lemma erasePair_orbits (p : Perm D) {a b : D} (hab : a ≠ b)
    (x y : {x // OffPair a b x}) :
    (erasePair p hab).SameCycle x y ↔ p.SameCycle x.val y.val := by
  rw [erasePair,sameCycle_subtypePerm]
  change (bypass (bypass p a) b).SameCycle x.val y.val ↔ _
  rw [bypass_orbits _ _ _ _ x.property.2 y.property.2,
    bypass_orbits _ _ _ _ x.property.1 y.property.1]

lemma card_offPair {a b : D} (hab : a ≠ b) :
    Fintype.card {x : D // OffPair a b x} + 2 = Fintype.card D := by
  have hc : Fintype.card {x : D // ¬ OffPair a b x} = 2 := by
    rw [Fintype.card_of_subtype ({a,b} : Finset D) (by intro x; simp only [Finset.mem_insert,Finset.mem_singleton,OffPair]; tauto)]
    simp [hab]
  have h := Fintype.card_subtype_compl (OffPair a b)
  omega

lemma erasePair_cycles (p : Perm D) {a b : D} (hab : a ≠ b)
    (ha : p a ≠ a) (hb : bypass p a b ≠ b) : cycles (erasePair p hab) = cycles p := by
  let q := bypassPair p a b
  have hqA : q a = a := bypassPair_a p hab
  have hqB : q b = b := bypassPair_b p a b
  let s := q.subtypePerm (p := fun x => ¬ OffPair a b x)
    (fun x => not_congr (offPair_invariant hqA hqB x))
  have hc : cycles q = cycles (erasePair p hab) + cycles s := by
    simpa only [cycles_eq_card_classes,erasePair,q,s] using
      (cycles_subtype_split (P := OffPair a b) q (offPair_invariant hqA hqB))
  have hs : s = 1 := by
    ext x
    change q x.val = x.val
    have hx : x.val = a ∨ x.val = b := by
      have hh := x.property
      unfold OffPair at hh
      tauto
    rcases hx with hx|hx
    · rw [hx,hqA]
    · rw [hx,hqB]
  have hcard : Fintype.card {x : D // ¬ OffPair a b x} = 2 := by
    rw [Fintype.card_of_subtype ({a,b} : Finset D) (by intro x; simp only [Finset.mem_insert,Finset.mem_singleton,OffPair]; tauto)]
    simp [hab]
  have hsC : cycles s = 2 := by rw [hs]; simp [cycles,defect,hcard]
  have hqC : cycles q = cycles p + 2 := by
    change cycles (bypass (bypass p a) b) = _
    rw [bypass_cycles,bypass_cycles,ite_eq_right hb,ite_eq_right ha]
    omega
  rw [hsC,hqC] at hc
  omega

end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
