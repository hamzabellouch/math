import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Order.Filter.AtTopBot.Basic
import OAI.NumberTheory.Jacobsthal.Model

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.Targets

open Filter
open scoped Topology

noncomputable def representationCount (A : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range (n + 1)).filter fun a => a ∈ A ∧ n - a ∈ A).card

noncomputable def orderedRepresentations (A : Set ℕ) (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range (n + 1)).product (Finset.range (n + 1))).filter
    fun r => r.1 ∈ A ∧ r.2 ∈ A ∧ r.1 + r.2 = n

theorem representationCount_eq_card_orderedRepresentations (A : Set ℕ) (n : ℕ) :
    representationCount A n = (orderedRepresentations A n).card := by
  classical
  unfold representationCount orderedRepresentations
  apply Finset.card_bij (fun a _ => (a, n - a))
  · intro a ha
    obtain ⟨harange, haA, hbA⟩ := Finset.mem_filter.mp ha
    have han := Finset.mem_range.mp harange
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨harange, Finset.mem_range.mpr (by omega)⟩,
      haA, hbA, ?_⟩
    omega
  · intro a₁ _ a₂ _ heq
    exact congrArg Prod.fst heq
  · intro r hr
    obtain ⟨hrange, hxA, hyA, hsum⟩ := Finset.mem_filter.mp hr
    have hxrange := (Finset.mem_product.mp hrange).1
    have hdiff : n - r.1 = r.2 := by omega
    refine ⟨r.1, Finset.mem_filter.mpr ⟨hxrange, hxA, ?_⟩, ?_⟩
    · simpa only [hdiff] using hyA
    · exact Prod.ext rfl hdiff

def LogarithmicRepresentationLimit : Prop :=
  ∃ A : Set ℕ, ∃ c : ℝ, c ≠ 0 ∧
    Tendsto (fun n : ℕ => (representationCount A n : ℝ) / Real.log n)
      atTop (𝓝 c)

def AdditiveBasisPiLimit : Prop :=
  ∃ A : Set ℕ,
    Tendsto (fun n : ℕ => (representationCount A n : ℝ) / Real.log n)
      atTop (𝓝 Real.pi)

theorem public_limit_of_pi_limit (h : AdditiveBasisPiLimit) :
    LogarithmicRepresentationLimit := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A, Real.pi, ne_of_gt Real.pi_pos, hA⟩

end NumberTheoryLean.Targets

end

end Erdos970

end OAI
