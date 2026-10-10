import Mathlib.Analysis.Calculus.MeanValue
import OAI.Geometry.NodalSets.Elliptic.RealCoordinateDerivativeNorm

namespace OAI

namespace Yau.Geometry
open Yau.Analysis Metric
open scoped ContDiff NNReal
noncomputable section

theorem real_partialJet_lipschitz (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W)
    (ds : List (Fin 4)) (y : Yau.Jets.Coord) (r : ℝ) (B : ℝ≥0)
    (hb : ∀ i : Fin 4, ∀ x ∈ closedBall y r, |partialJet W (i::ds) x| ≤ B) :
    LipschitzOnWith (4*B) (partialJet W ds) (closedBall y r) := by
  apply (convex_closedBall y r).lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ ↦ (partialJet_smooth W hW ds).differentiable (by simp) x)
  intro x hx
  have h := iteratedFDeriv_norm_le_coordinate_bound (partialJet W ds)
    (partialJet_smooth W hW ds) 1 x B B.coe_nonneg (by
      intro es hes
      obtain ⟨i,rfl⟩ := List.length_eq_one_iff.mp hes
      exact hb i x hx)
  rw [pow_one,norm_iteratedFDeriv_one] at h
  exact_mod_cast h

end
end Yau.Geometry

end OAI
