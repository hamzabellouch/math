import OAI.LinearAlgebra.MatrixMultiplication.Completion.Conditioning

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

namespace MatrixMultiplication.CompletionLaws

open MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq

variable {A X : Type*} [Fintype A] [Fintype X]

def uniformOn (P : X → Prop) [Nonempty {x // P x}] : FiniteLaw X where
  mass x := if P x then (Fintype.card {x // P x} : ℝ)⁻¹ else 0
  nonneg x := by split_ifs; exact inv_nonneg.mpr (Nat.cast_nonneg _); exact le_rfl
  total := by
    rw [← sum_subtype_indicator P (fun _ => (Fintype.card {x // P x} : ℝ)⁻¹)]
    have hc : (Fintype.card {x // P x} : ℝ) ≠ 0 :=
      (Nat.cast_pos.mpr Fintype.card_pos).ne'
    simp [hc]

theorem uniformOn_mass (P : X → Prop) [Nonempty {x // P x}] (x : X) :
    (uniformOn P).mass x = if P x then (Fintype.card {x // P x} : ℝ)⁻¹ else 0 := rfl

def UniformCoordinate (p : FiniteLaw A) (f : A → X) (P : X → Prop) : Prop :=
  ∀ x, (p.map f).mass x = if P x then (Fintype.card {x // P x} : ℝ)⁻¹ else 0

theorem uniformOn_entropy (P : X → Prop) [Nonempty {x // P x}] :
    finiteEntropy (uniformOn P).mass = Real.log (Fintype.card {x // P x}) := by
  calc
    _ = ∑ x, if P x then entropyTerm (Fintype.card {x // P x} : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : P x <;> simp [uniformOn_mass, hx]
    _ = ∑ _x : {x // P x}, entropyTerm (Fintype.card {x // P x} : ℝ)⁻¹ :=
      (sum_subtype_indicator P _).symm
    _ = _ := finiteEntropy_uniform

theorem uniform_coordinate_entropy (p : FiniteLaw A) (f : A → X) (P : X → Prop)
    (h : UniformCoordinate p f P) :
    finiteEntropy (p.map f).mass = Real.log (Fintype.card {x // P x}) := by
  calc
    _ = ∑ x, if P x then entropyTerm (Fintype.card {x // P x} : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [h x]
      split_ifs <;> simp
    _ = ∑ _x : {x // P x}, entropyTerm (Fintype.card {x // P x} : ℝ)⁻¹ :=
      (sum_subtype_indicator P _).symm
    _ = _ := finiteEntropy_uniform

theorem uniform_coordinate_eventMass (p : FiniteLaw A) (f : A → X)
    (P Q : X → Prop) (h : UniformCoordinate p f P) :
    eventMass p (fun a => Q (f a)) =
      (Fintype.card {x // P x ∧ Q x} : ℝ) / Fintype.card {x // P x} := by
  rw [eventMass_coordinate]
  unfold eventMass
  have hmass : (∑ x : {x // Q x}, (p.map f).mass x.val) =
      ∑ x : {x // Q x}, if P x.val then (Fintype.card {x // P x} : ℝ)⁻¹ else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    exact h x.val
  rw [hmass, sum_subtype_indicator Q
    (fun x => if P x then (Fintype.card {x // P x} : ℝ)⁻¹ else 0)]
  have hsum : (∑ x, if Q x then
      (if P x then (Fintype.card {x // P x} : ℝ)⁻¹ else 0) else 0) =
      ∑ x, if P x ∧ Q x then (Fintype.card {x // P x} : ℝ)⁻¹ else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hp : P x <;> by_cases hq : Q x <;> simp [hp, hq]
  rw [hsum, ← sum_subtype_indicator (fun x => P x ∧ Q x)
    (fun _ => (Fintype.card {x // P x} : ℝ)⁻¹)]
  simp [div_eq_mul_inv]

theorem uniform_coordinate_condition (p : FiniteLaw A) (f : A → X)
    (P Q : X → Prop) (h : UniformCoordinate p f P)
    (hP : 0 < Fintype.card {x // P x})
    (hPQ : 0 < Fintype.card {x // P x ∧ Q x}) :
    ∃ hevent : 0 < eventMass p (fun a => Q (f a)),
      UniformCoordinate (condition p (fun a => Q (f a)) hevent)
        (fun a => f a.val) (fun x => P x ∧ Q x) := by
  have hP' : (0 : ℝ) < Fintype.card {x // P x} := Nat.cast_pos.mpr hP
  have hPQ' : (0 : ℝ) < Fintype.card {x // P x ∧ Q x} := Nat.cast_pos.mpr hPQ
  have hevent : 0 < eventMass p (fun a => Q (f a)) := by
    rw [uniform_coordinate_eventMass p f P Q h]
    exact div_pos hPQ' hP'
  refine ⟨hevent, fun x => ?_⟩
  rw [condition_coordinate_mass, h x, uniform_coordinate_eventMass p f P Q h]
  by_cases hp : P x <;> by_cases hq : Q x <;> simp [hp, hq]
  rw [div_div_eq_mul_div, inv_mul_cancel₀ hP'.ne', one_div]

end MatrixMultiplication.CompletionLaws

end

end OAI
