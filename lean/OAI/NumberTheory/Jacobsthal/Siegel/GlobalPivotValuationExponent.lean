import Mathlib
import PrimeNumberTheoremAnd.Erdos970.HadamardSupport
import OAI.NumberTheory.Jacobsthal.Siegel.GreedyPivotsWeightLowSpan

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
namespace WeightedTorusJets

theorem global_pivot_valuation_exponent_eq {ι : Type*} [Fintype ι]
    (α : ι ↪ (Fin 3 → ℕ)) (P : Finset (Fin 3 → ℕ))
    (hP : Set.range α = (P : Set (Fin 3 → ℕ))) (p : ℕ) :
    (∑ i, α i 0 / p) = ∑ a ∈ P, ⌊(a 0 : ℝ) / p⌋₊ := by
  rw [sum_embedding_eq_sum_finset_of_range α P hP (fun a => a 0 / p)]
  simp only [Nat.floor_div_eq_div]



theorem global_pivot_valuation_exponent_cast_eq {ι : Type*} [Fintype ι]
    (α : ι ↪ (Fin 3 → ℕ)) (P : Finset (Fin 3 → ℕ))
    (hP : Set.range α = (P : Set (Fin 3 → ℕ))) (p : ℕ) :
    ((∑ i, α i 0 / p : ℕ) : ℝ) = ∑ a ∈ P, (⌊(a 0 : ℝ) / p⌋ : ℝ) := by
  rw [global_pivot_valuation_exponent_eq α P hP p, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact natCast_floor_eq_intCast_floor (by positivity)

end WeightedTorusJets

end

end Erdos970

end OAI
