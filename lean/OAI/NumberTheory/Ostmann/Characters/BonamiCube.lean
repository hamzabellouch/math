import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Basic
import OAI.NumberTheory.Ostmann.Characters.BonamiMean
import OAI.NumberTheory.Ostmann.Construction.FiniteEnumeration

namespace OAI

/-! # Concrete finite Boolean polynomials for Bonami's inequality -/

namespace Ostmann

open Finset
open scoped Classical BigOperators

noncomputable def booleanPolynomial {α : Type*} [Fintype α]
    (a : (α → Bool) → ℝ) (ε : α → Bool) : ℝ :=
  ∑ b : α → Bool, a b * ∏ i : α, if b i then (if ε i then 1 else -1) else 1

noncomputable def booleanEnergy {α : Type*} [Fintype α]
    (r : ℝ) (a : (α → Bool) → ℝ) : ℝ :=
  ∑ b : α → Bool, (∏ i : α, if b i then r else 1) * (a b) ^ 2

theorem booleanEnergy_nonneg {α : Type*} [Fintype α]
    (r : ℝ) (hr : 0 ≤ r) (a : (α → Bool) → ℝ) : 0 ≤ booleanEnergy r a := by
  apply sum_nonneg
  intro b hb
  apply mul_nonneg _ (sq_nonneg _)
  exact prod_nonneg (fun i hi => by split <;> positivity)

theorem booleanPolynomial_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (a : (β → Bool) → ℝ) (ε : β → Bool) :
    booleanPolynomial a ε =
      booleanPolynomial (fun b : α → Bool => a (fun i => b (e.symm i)))
        (fun i => ε (e i)) := by
  unfold booleanPolynomial
  rw [← (Equiv.arrowCongr e (Equiv.refl Bool)).sum_comp]
  apply sum_congr rfl
  intro b hb
  congr 1
  rw [← e.prod_comp]
  simp [Equiv.arrowCongr]

theorem booleanEnergy_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (r : ℝ) (a : (β → Bool) → ℝ) :
    booleanEnergy r a =
      booleanEnergy r (fun b : α → Bool => a (fun i => b (e.symm i))) := by
  unfold booleanEnergy
  rw [← (Equiv.arrowCongr e (Equiv.refl Bool)).sum_comp]
  apply sum_congr rfl
  intro b hb
  congr 1
  rw [← e.prod_comp]
  simp [Equiv.arrowCongr]

theorem sum_option_cube {α : Type*} [Fintype α] (f : (Option α → Bool) → ℝ) :
    (∑ b : Option α → Bool, f b) =
      (∑ b : α → Bool, f (fun i => i.elim true b)) +
        ∑ b : α → Bool, f (fun i => i.elim false b) := by
  calc
    _ = ∑ z : Bool × (α → Bool),
        f ((Equiv.piOptionEquivProd (β := fun _ : Option α => Bool)).symm z) :=
      ((Equiv.piOptionEquivProd (β := fun _ : Option α => Bool)).symm.sum_comp f).symm
    _ = ∑ x : Bool, ∑ b : α → Bool, f (fun i => i.elim x b) := by
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro x hx
      apply sum_congr rfl
      intro b hb
      congr 1
      funext i
      cases i <;> rfl
    _ = _ := Fintype.sum_bool _

theorem booleanPolynomial_option {α : Type*} [Fintype α]
    (a : (Option α → Bool) → ℝ) (ε : Option α → Bool) :
    booleanPolynomial a ε =
      booleanPolynomial (fun b => a (fun i => i.elim false b)) (fun i => ε (some i)) +
        (if ε none then 1 else -1) *
          booleanPolynomial (fun b => a (fun i => i.elim true b)) (fun i => ε (some i)) := by
  unfold booleanPolynomial
  have hs := sum_option_cube (fun b : Option α → Bool =>
    a b * ∏ i : Option α, if b i then (if ε i then 1 else -1) else 1)
  have hp : ∀ f : Option α → ℝ, (∏ i, f i) = f none * ∏ i : α, f (some i) :=
    fun f => Fintype.prod_option f
  simp only [finite_univ_canonical] at hs ⊢
  simp only [finite_univ_canonical] at hp
  rw [hs]
  simp only [hp, Option.elim, Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro b hb
  ac_rfl

theorem booleanEnergy_option {α : Type*} [Fintype α]
    (r : ℝ) (a : (Option α → Bool) → ℝ) :
    booleanEnergy r a =
      booleanEnergy r (fun b => a (fun i => i.elim false b)) +
        r * booleanEnergy r (fun b => a (fun i => i.elim true b)) := by
  unfold booleanEnergy
  have hs := sum_option_cube (fun b : Option α → Bool =>
    (∏ i : Option α, if b i then r else 1) * (a b) ^ 2)
  have hp : ∀ f : Option α → ℝ, (∏ i, f i) = f none * ∏ i : α, f (some i) :=
    fun f => Fintype.prod_option f
  simp only [finite_univ_canonical] at hs ⊢
  simp only [finite_univ_canonical] at hp
  rw [hs]
  simp only [hp, Option.elim, Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro b hb
  simp only [mul_assoc]
  rw [add_comm]
  congr 3

end Ostmann

end OAI
