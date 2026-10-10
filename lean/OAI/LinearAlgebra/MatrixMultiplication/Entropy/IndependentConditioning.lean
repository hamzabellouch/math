import OAI.LinearAlgebra.MatrixMultiplication.Tensor.UniformCoordinate

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.CompletionLaws

open MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq

variable {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]

theorem condition_map_mass (p : FiniteLaw A) (P : A → Prop)
    (h : 0 < eventMass p P) (f : A → X) (x : X) :
    ((condition p P h).map (fun a => f a.val)).mass x =
      (∑ a : {a // P a}, if f a.val = x then p.mass a.val else 0) / eventMass p P := by
  rw [FiniteLaw.map_mass, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  rw [condition_mass]
  split_ifs <;> simp

theorem joint_event_sum (p : FiniteLaw A) (f : A → X) (g : A → B)
    (Q : B → Prop) (x : X) :
    (∑ a : {a // Q (g a)}, if f a.val = x then p.mass a.val else 0) =
      ∑ b : {b // Q b}, (p.map (fun a => (f a, g a))).mass (x, b.val) := by
  rw [sum_subtype_indicator (fun a => Q (g a))
    (fun a => if f a = x then p.mass a else 0),
    sum_subtype_indicator Q
      (fun b => (p.map (fun a => (f a, g a))).mass (x, b))]
  simp only [FiniteLaw.map_mass, Prod.mk.injEq]
  calc
    (∑ a, if Q (g a) then (if f a = x then p.mass a else 0) else 0) =
        ∑ a, ∑ b, if Q b then (if f a = x ∧ g a = b then p.mass a else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single (g a)]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    _ = ∑ b, ∑ a, if Q b then (if f a = x ∧ g a = b then p.mass a else 0) else 0 :=
      Finset.sum_comm
    _ = ∑ b, if Q b then ∑ a, if f a = x ∧ g a = b then p.mass a else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> simp

theorem condition_independent_coordinate_mass (p : FiniteLaw A)
    (f : A → X) (g : A → B) (Q : B → Prop)
    (independent : ∀ x b, (p.map (fun a => (f a, g a))).mass (x, b) =
      (p.map f).mass x * (p.map g).mass b)
    (h : 0 < eventMass p (fun a => Q (g a))) (x : X) :
    ((condition p (fun a => Q (g a)) h).map (fun a => f a.val)).mass x =
      (p.map f).mass x := by
  rw [condition_map_mass, joint_event_sum]
  simp_rw [independent]
  rw [← Finset.mul_sum]
  change ((p.map f).mass x * eventMass (p.map g) Q) /
      eventMass p (fun a => Q (g a)) = _
  rw [← eventMass_coordinate p g Q, mul_div_cancel_right₀ _ h.ne']

theorem uniform_coordinate_independent_condition (p : FiniteLaw A)
    (f : A → X) (g : A → B) (P : X → Prop) (Q : B → Prop)
    (uniform : UniformCoordinate p f P)
    (independent : ∀ x b, (p.map (fun a => (f a, g a))).mass (x, b) =
      (p.map f).mass x * (p.map g).mass b)
    (h : 0 < eventMass p (fun a => Q (g a))) :
    UniformCoordinate (condition p (fun a => Q (g a)) h)
      (fun a => f a.val) P := by
  intro x
  rw [condition_independent_coordinate_mass p f g Q independent h]
  exact uniform x

end MatrixMultiplication.CompletionLaws

end

end OAI
