import OAI.Combinatorics.CliqueFree.WalkEntropy
import OAI.Combinatorics.CliqueFree.TriangleState

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

namespace LocalWalk
open FiniteEntropy FiniteKernel
variable {G : SimpleGraph V} {w : V → ℝ}
lemma triangle_pair_sum [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v)
    (f : EdgeState G → EdgeState G → ℝ) :
    (∑ t : TriangleState G, TriangleState.weight w t * f t.edge12 t.edge13) =
      normalizer G w * ∑ e, law G w e * ∑ z, transition G w e z * f e z := by
  rw [TriangleState.corner_sum]
  simp only [mul_sum]
  apply sum_congr rfl
  intro e _
  apply sum_congr rfl
  intro z _
  have he := (hc _ _ e.adj).ne'
  have hZ := (normalizer_pos hw hc).ne'
  by_cases hs : e.src = z.src
  · by_cases ha : G.Adj e.dst z.dst
    · simp only [hs, ha, true_and, ↓reduceIte, transition, law]
      rw [hs] at he
      field_simp
    · simp [hs, ha, transition]
  · simp [hs, transition]

lemma triangle_edge_sum [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v) (f : EdgeState G → ℝ) :
    (∑ t : TriangleState G, TriangleState.weight w t * f t.edge12) =
      normalizer G w * ∑ e, law G w e * f e := by
  rw [triangle_pair_sum hw hc (fun e _ ↦ f e)]
  simp only [← sum_mul, (transition_stochastic hw hc _).2, one_mul]
end LocalWalk

end CliqueFreeIndependence.WeightedGraph

end

end OAI
