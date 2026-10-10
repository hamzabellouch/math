import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.BadClusters
import OAI.Probability.LatticeSurface.Coercivity.FilledHull
import OAI.Probability.LatticeSurface.Coercivity.GridClosedLabels
import OAI.Probability.LatticeSurface.Coercivity.HoleEdges
import OAI.Probability.LatticeSurface.Coercivity.HoleExtension
import OAI.Probability.LatticeSurface.Coercivity.HoleGeometry
import OAI.Probability.LatticeSurface.Coercivity.HoleIncident
import OAI.Probability.LatticeSurface.Coercivity.HoleSize
import OAI.Probability.LatticeSurface.Coercivity.HoleStar
import OAI.Probability.LatticeSurface.Coercivity.HullMore
import OAI.Probability.LatticeSurface.Coercivity.HullRims
import OAI.Probability.LatticeSurface.Coercivity.OuterHulls
import OAI.Probability.LatticeSurface.Convexity.WeightedHolder

namespace OAI

noncomputable section

open scoped BigOperators

namespace SparseHoles

theorem finite_hole_weighted (B : Finset Vertex) (lo hi : Vertex) (hB : B ⊆ box lo hi)
    (u : Vertex → ℝ) (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (E : Finset Edge) (hE : ∀ e∈E, e∈grid.edgeSet)
    (a : Edge → ℝ) (ha : ∀ e, 0 < a e) :
    let L := outerHulls (badClusters B) lo hi
    ∃ F : Finset Edge, (∀ e∈F, goodEdge L e) ∧
      (∑ e∈E, (edgeAbs (extension L u) e)^p)^(1/p) ≤
        (∑ e∈F, a e*(edgeAbs u e)^2)^(1/2:ℝ) *
        (∑ e∈F, (holeWeights L p e)^(2/(2-p))*(a e)^(-p/(2-p)))^((2-p)/(2*p)) ∧
      ∀ e, 1 ≤ holeWeights L p e ∧
        holeWeights L p e ≤ (1+128*32^(p-1))*(1+(edgeDiameter L e:ℝ))^(2*p) := by
  dsimp only
  let L := outerHulls (badClusters B) lo hi
  have hL : HoleFamily L := outer_hole_family _ lo hi (badClusters_family B lo hi hB)
  obtain ⟨F,hFg,henergy,hweights⟩ := hole_extension_energy L hL u p hp E hE
  refine ⟨F,hFg,?_,hweights⟩
  refine (Real.rpow_le_rpow (Finset.sum_nonneg fun e he => Real.rpow_nonneg (edgeAbs_nonneg _ _) _) henergy (by positivity)).trans ?_
  exact weighted_holder F a (holeWeights L p) (edgeAbs u) (fun e he => ha e)
    (fun e he => zero_le_one.trans (hweights e).1) (fun e he => edgeAbs_nonneg u e) p hp hp2

end SparseHoles

end

end OAI
