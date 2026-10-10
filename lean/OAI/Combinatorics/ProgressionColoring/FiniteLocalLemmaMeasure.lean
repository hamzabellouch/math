import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic

namespace OAI

open scoped BigOperators

universe uOmega

namespace QuantitativeVanDerWaerden.FiniteLocalLemma

/-- A probability on the finite sample space `Ω`, with the event identities
needed by the finite local lemma. -/
structure Probability (Ω : Type uOmega) [Fintype Ω] [DecidableEq Ω] where
  mass : Finset Ω → ℝ
  nonneg : ∀ A, 0 ≤ mass A
  univ : mass Finset.univ = 1
  mono : ∀ {A B}, A ⊆ B → mass A ≤ mass B
  split : ∀ A B, mass (A \ B) + mass (A ∩ B) = mass A

namespace Probability

variable {Ω : Type uOmega} [Fintype Ω] [DecidableEq Ω]

@[simp]
theorem mass_empty (P : Probability Ω) : P.mass ∅ = 0 := by
  have h : P.mass ∅ + P.mass ∅ = P.mass ∅ := by
    simpa using P.split ∅ ∅
  exact add_left_cancel (h.trans (add_zero _).symm)

/-- The probability whose mass at each point is its prescribed weight. -/
noncomputable def ofWeights (weight : Ω → ℝ)
    (weight_nonneg : ∀ ω, 0 ≤ weight ω)
    (weight_sum : ∑ ω, weight ω = 1) : Probability Ω where
  mass A := ∑ ω ∈ A, weight ω
  nonneg A := Finset.sum_nonneg fun ω _ => weight_nonneg ω
  univ := weight_sum
  mono := by
    intro A B hAB
    exact Finset.sum_le_sum_of_subset_of_nonneg hAB fun ω _ _ => weight_nonneg ω
  split A B := by
    exact (add_comm _ _).trans (Finset.sum_inter_add_sum_sdiff A B weight)

@[simp]
theorem ofWeights_mass (weight : Ω → ℝ)
    (weight_nonneg : ∀ ω, 0 ≤ weight ω)
    (weight_sum : ∑ ω, weight ω = 1) (A : Finset Ω) :
    (ofWeights weight weight_nonneg weight_sum).mass A = ∑ ω ∈ A, weight ω := rfl

end Probability

end QuantitativeVanDerWaerden.FiniteLocalLemma

end OAI
