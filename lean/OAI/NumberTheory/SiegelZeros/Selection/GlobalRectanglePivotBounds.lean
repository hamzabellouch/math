import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Selection.GreedyPivotsWeightLowSpan

namespace OAI

namespace SiegelZeros

namespace WeightedTorusJets

open scoped BigOperators

theorem global_source_rectangle_pivot_bounds {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (H N : ℕ) (hH : 0 < H)
    (hHN : H ≤ N) (hN : 18818 ≤ N) (R : (Fin 3 → ℕ) → V)
    (e : ℕ ≃ (Fin 3 → ℕ))
    (he : Monotone (fun i => (e i) 0 + H * (e i) 1 + H * (e i) 2))
    (α : Fin (N ^ 4) ↪ (Fin 3 → ℕ))
    (hα : Set.range α =
      ((greedyPivots K (R ∘ e) (weightedJetIndices H (N ^ 4 - 1)).card).image e :
        Set (Fin 3 → ℕ)))
    (hspan : Submodule.span K (R '' {a : Fin 3 → ℕ |
      (a 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
      (a 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) ∧
      (a 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ)}) = ⊤) :
    let P := (greedyPivots K (R ∘ e) (weightedJetIndices H (N ^ 4 - 1)).card).image e
    (N : ℝ) ^ 4 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) /
        (4 * 97 ^ 2) ≤ ∑ a ∈ P, (a 0 : ℝ) ∧
      (∑ a ∈ P, ((a 1 : ℝ) + a 2)) ≤
        192 * (N : ℝ) ^ 4 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) := by
  classical
  dsimp only
  let s := weightedJetIndices H (N ^ 4 - 1)
  let w := fun a : Fin 3 → ℕ => a 0 + H * a 1 + H * a 2
  let P := (greedyPivots K (R ∘ e) s.card).image e
  have hs : ∀ a, a ∈ s ↔ w a ≤ N ^ 4 - 1 := mem_weightedJetIndices_iff hH
  let e₀ := restrictWeightSortedEquiv s w (N ^ 4 - 1) hs e he
  have hmap : Finset.univ.map α = P := by
    apply Finset.coe_injective
    rw [Finset.coe_map, Finset.coe_univ, Set.image_univ]
    exact hα
  have hcard : P.card = N ^ 4 := by rw [← hmap]; simp
  have hfinite := finiteGreedyPivots_restrictWeightSortedEquiv
    (K := K) s R w (N ^ 4 - 1) hs e he 0
  change finiteGreedyPivots K s R e₀ 0 = P at hfinite
  apply weighted_pivot_bounds P H N hH hHN hN hcard
  intro a ha
  apply fixed_first_greedy_rectangle_weight_bound H N hH R e₀
    (restrictWeightSortedEquiv_monotone s w (N ^ 4 - 1) hs e he) hspan a
  rw [hfinite]
  exact ha

end WeightedTorusJets


end SiegelZeros

end OAI
