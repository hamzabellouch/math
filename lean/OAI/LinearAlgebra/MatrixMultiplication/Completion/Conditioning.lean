import OAI.LinearAlgebra.MatrixMultiplication.Completion.Laws

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionLaws

open MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {A X : Type*} [Fintype A] [Fintype X]

theorem sum_subtype_indicator (P : A → Prop) (f : A → ℝ) :
    (∑ a : {a // P a}, f a.val) = ∑ a, if P a then f a else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

def eventMass (p : FiniteLaw A) (P : A → Prop) : ℝ :=
  ∑ a : {a // P a}, p.mass a.val

theorem eventMass_nonneg (p : FiniteLaw A) (P : A → Prop) : 0 ≤ eventMass p P :=
  Finset.sum_nonneg fun a _ => p.nonneg a.val

def condition (p : FiniteLaw A) (P : A → Prop) (h : 0 < eventMass p P) :
    FiniteLaw {a // P a} where
  mass a := p.mass a.val / eventMass p P
  nonneg a := div_nonneg (p.nonneg a.val) h.le
  total := by rw [← Finset.sum_div]; exact div_self h.ne'

theorem condition_mass (p : FiniteLaw A) (P : A → Prop)
    (h : 0 < eventMass p P) (a : {a // P a}) :
    (condition p P h).mass a = p.mass a.val / eventMass p P := rfl

theorem condition_coordinate_mass (p : FiniteLaw A) (f : A → X) (Q : X → Prop)
    (h : 0 < eventMass p (fun a => Q (f a))) (x : X) :
    ((condition p (fun a => Q (f a)) h).map (fun a => f a.val)).mass x =
      if Q x then (p.map f).mass x / eventMass p (fun a => Q (f a)) else 0 := by
  rw [FiniteLaw.map_mass]
  simp only [condition_mass]
  have hsum :
      (∑ a : {a // Q (f a)}, if f a.val = x then
        p.mass a.val / eventMass p (fun a => Q (f a)) else 0) =
      ∑ a, if Q (f a) then
        (if f a = x then p.mass a / eventMass p (fun a => Q (f a)) else 0) else 0 :=
    sum_subtype_indicator (fun a => Q (f a))
      (fun a => if f a = x then p.mass a / eventMass p (fun a => Q (f a)) else 0)
  rw [hsum]
  by_cases hx : Q x
  · rw [ite_eq_left hx, FiniteLaw.map_mass, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : f a = x
    · simp [ha, hx]
    · simp [ha]
  · rw [ite_eq_right hx]
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : f a = x
    · simp [ha, hx]
    · simp [ha]

theorem eventMass_coordinate (p : FiniteLaw A) (f : A → X) (Q : X → Prop) :
    eventMass p (fun a => Q (f a)) = eventMass (p.map f) Q := by
  rw [eventMass, eventMass, sum_subtype_indicator, sum_subtype_indicator]
  simp only [FiniteLaw.map_mass]
  calc
    (∑ a, if Q (f a) then p.mass a else 0) =
        ∑ a, ∑ x, if Q x then (if f a = x then p.mass a else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single (f a)]
      · simp
      · intro x _ hne
        simp [Ne.symm hne]
      · simp
    _ = ∑ x, ∑ a, if Q x then (if f a = x then p.mass a else 0) else 0 :=
      Finset.sum_comm
    _ = ∑ x, if Q x then ∑ a, if f a = x then p.mass a else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp

def transport {B : Type*} [Fintype B] (e : A ≃ B) (p : FiniteLaw A) : FiniteLaw B :=
  p.map e

theorem transport_mass {B : Type*} [Fintype B] (e : A ≃ B) (p : FiniteLaw A) (a : A) :
    (transport e p).mass (e a) = p.mass a := p.map_mass_apply e e.injective a

theorem transport_entropy {B : Type*} [Fintype B] (e : A ≃ B) (p : FiniteLaw A) :
    finiteEntropy (transport e p).mass = finiteEntropy p.mass :=
  p.map_entropy_of_injective e e.injective

end MatrixMultiplication.CompletionLaws

end

end OAI
