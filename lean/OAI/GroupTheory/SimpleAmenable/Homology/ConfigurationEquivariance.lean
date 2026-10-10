import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.Configuration

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ConfigurationEquivariance
open Classical Finsupp
namespace ConfigurationChains
variable {V W Z : Type*}

noncomputable def push (f : V → W) : Chain V →ₗ[ℤ] Chain W :=
  Finsupp.lmapDomain ℤ ℤ (List.map f)

@[simp] theorem push_single (f : V → W) (l : List V) (n : ℤ) :
    push f (single l n)=single (l.map f) n := by simp [push]

@[simp] theorem push_id (c : Chain V) : push id c=c := by
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l n c hl hn ih => simp [ih]

@[simp] theorem push_comp (g : W → Z) (f : V → W) (c : Chain V) :
    push g (push f c)=push (g ∘ f) c := by
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l n c hl hn ih => simp [ih, List.map_map]

theorem push_cone (f : V → W) (v : V) (c : Chain V) :
    push f (cone v c)=cone (f v) (push f c) := by
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l n c hl hn ih => simp [ih]

theorem push_faceSum (f : V → W) (l : List V) :
    push f (faceSum l)=faceSum (l.map f) := by
  induction l with
  | nil => simp [faceSum]
  | cons v l ih => simp [faceSum,push_cone,ih]

theorem push_boundary (f : V → W) (c : Chain V) :
    push f (boundary c)=boundary (push f c) := by
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l n c hl hn ih => simp [push_faceSum,ih]

theorem push_admissible {R : V → V → Prop} {S : W → W → Prop}
    (f : V → W) (hf : ∀v w,R v w → S (f v) (f w)) {n : ℕ} {c : Chain V}
    (hc : Admissible R n c) : Admissible S n (push f c) := by
  intro l hl
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hl)
  exact ⟨List.pairwise_map.mpr ((hc k hk).1.imp (fun h => hf _ _ h)),
    by simpa only [List.length_map] using (hc k hk).2⟩

noncomputable def degree (R : V → V → Prop) (n : ℕ) : Submodule ℤ (Chain V) where
  carrier := {c | Admissible R n c}
  zero_mem' := admissible_zero R n
  add_mem' := by
    intro c d hc hd l hl
    rcases Finset.mem_union.mp (Finsupp.support_add hl) with hl|hl
    · exact hc l hl
    · exact hd l hl
  smul_mem' := by
    intro k c hc l hl
    exact hc l (Finsupp.support_smul hl)

@[simp] theorem mem_degree {R : V → V → Prop} {n : ℕ} {c : Chain V} :
    c∈degree R n ↔ Admissible R n c := Iff.rfl

noncomputable def degreeBoundary (R : V → V → Prop) (n : ℕ) :
    degree R (n+1) →ₗ[ℤ] degree R n :=
  boundary.restrict (fun _ h => admissible_boundary h)

@[simp] theorem degreeBoundary_val {R : V → V → Prop} {n : ℕ}
    (c : degree R (n+1)) : (degreeBoundary R n c).val=boundary c.val := rfl

@[simp] theorem degreeBoundary_square (R : V → V → Prop) (n : ℕ)
    (c : degree R (n+2)) : degreeBoundary R n (degreeBoundary R (n+1) c)=0 := by
  apply Subtype.ext
  exact boundary_boundary c.val

noncomputable def degreePush {R : V → V → Prop} {S : W → W → Prop}
    (f : V → W) (hf : ∀v w,R v w → S (f v) (f w)) (n : ℕ) :
    degree R n →ₗ[ℤ] degree S n :=
  (push f).restrict (fun _ h => push_admissible f hf h)

@[simp] theorem degreePush_val {R : V → V → Prop} {S : W → W → Prop}
    (f : V → W) (hf : ∀v w,R v w → S (f v) (f w)) (n : ℕ)
    (c : degree R n) : (degreePush f hf n c).val=push f c.val := rfl

theorem degreePush_boundary {R : V → V → Prop} {S : W → W → Prop}
    (f : V → W) (hf : ∀v w,R v w → S (f v) (f w)) (n : ℕ)
    (c : degree R (n+1)) :
    degreePush f hf n (degreeBoundary R n c)=
      degreeBoundary S n (degreePush f hf (n+1) c) := by
  apply Subtype.ext
  exact push_boundary f c.val

end ConfigurationChains
end ConfigurationEquivariance

end SimpleAmenable
end
end

end OAI
