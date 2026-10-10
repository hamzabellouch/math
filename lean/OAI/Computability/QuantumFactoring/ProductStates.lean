import Mathlib
import OAI.Computability.QuantumFactoring.ExactnessFurther

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness

/-- Independent, not necessarily identically distributed, retained registers. -/
noncomputable def productState {ι : Type*} [Fintype ι] {α : ι → Type*}
    (ψ : ∀ i, α i → ℂ) (x : ∀ i, α i) : ℂ := ∏ i, ψ i (x i)

lemma productState_normalized {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (ψ : ∀ i, α i → ℂ)
    (hψ : ∀ i, ∑ x, Complex.normSq (ψ i x)=1) :
    ∑ x, Complex.normSq (productState ψ x)=1 := by
  simp only [productState,map_prod]
  rw [←Fintype.prod_sum (fun i a => Complex.normSq (ψ i a))]
  simp only [hψ,Finset.prod_const_one]

lemma productState_all_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (ψ : ∀ i, α i → ℂ)
    (P : ∀ i, α i → Prop) :
    outcomeMass (fun x => ∀ i, P i (x i)) (productState ψ)=
      ∏ i, outcomeMass (P i) (ψ i) := by
  classical
  unfold outcomeMass productState
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ∀ i, P i (x i)
  · simp [hx,map_prod]
  · rw [ite_eq_right hx]
    obtain ⟨i,hi⟩ := not_forall.mp hx
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm

lemma productState_constant_mass {α : Type*} [Fintype α] {K : ℕ}
    (ψ : Fin K → α → ℂ) (P : Fin K → α → Prop) (z : ℝ)
    (hz : ∀ i, outcomeMass (P i) (ψ i)=z) :
    outcomeMass (fun x => ∀ i, P i (x i)) (productState ψ)=z^K := by
  rw [productState_all_mass]
  simp only [hz,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

end ExactQuantumFactoring


end

end OAI
