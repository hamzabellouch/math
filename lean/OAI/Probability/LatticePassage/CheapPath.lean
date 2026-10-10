import OAI.Probability.LatticePassage.ExponentialMoment
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V}

def pathEdges {x y : V} : G.Walk x y → List G.edgeSet
  | .nil => []
  | .cons h p => ⟨s(_, _), h⟩ :: pathEdges p

lemma pathEdges_val {x y : V} (p : G.Walk x y) :
    (pathEdges p).map Subtype.val = p.edges := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [pathEdges, ih]

lemma pathEdges_length {x y : V} (p : G.Walk x y) :
    (pathEdges p).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [pathEdges, ih]

lemma pathEdges_nodup {x y : V} {p : G.Walk x y} (hp : p.IsTrail) :
    (pathEdges p).Nodup := by
  apply List.Nodup.of_map (f := Subtype.val)
  rw [pathEdges_val]
  exact hp.edges_nodup

lemma pathCost_eq_edgeList_sum (ω : Weights G) {x y : V} (p : G.Walk x y) :
    pathCost ω p = ((pathEdges p).map ω).sum := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [pathEdges, pathCost, edgeCost, ih]

theorem cheap_trail_probability {x y : Vertex} (p : lattice.Walk x y) (hp : p.IsTrail)
    (t : ℝ) : environmentLaw {ω : Environment | pathCost ω p ≤ t} ≤
      ENNReal.ofReal (1 / 6 : ℝ) ^ p.length / ENNReal.ofReal (exp (-5 * t)) := by
  classical
  have hn := pathEdges_nodup hp
  have hc : (pathEdges p).toFinset.card = p.length := by
    rw [List.toFinset_card_of_nodup hn, pathEdges_length]
  have he : ∀ ω : Environment, (∑ e ∈ (pathEdges p).toFinset, ω e) = pathCost ω p := by
    intro ω
    rw [pathCost_eq_edgeList_sum]
    exact List.sum_toFinset _ hn
  have h := cheap_edge_set_probability (pathEdges p).toFinset t
  simpa only [he, hc] using h

end CompanionFPP

end OAI
