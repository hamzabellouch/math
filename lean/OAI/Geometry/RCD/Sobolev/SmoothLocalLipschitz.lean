import OAI.Geometry.RCD.Sobolev.InteriorSmoothTestBounds
import Mathlib.Topology.UniformSpace.HeineCantor

namespace OAI

/-! # Uniform local Lipschitz bounds from the actual differential of a compact smooth test -/

open Set Metric
open scoped ContDiff NNReal
noncomputable section
namespace RegularPointCoordinates

theorem compact_smooth_local_lipschitz {n : ℕ} {ψ : Euclidean n → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) {η : ℝ} (hη : 0<η) :
    ∃ δ : ℝ, 0<δ ∧ ∀ z : Euclidean n,
      LipschitzOnWith (‖fderiv ℝ ψ z‖₊+⟨η,hη.le⟩) ψ (closedBall z δ) := by
  have hu : UniformContinuous (fderiv ℝ ψ) :=
    (hs.fderiv ℝ).uniformContinuous_of_continuous (hψ.continuous_fderiv (by norm_num))
  obtain ⟨d,hd,hclose⟩ := Metric.uniformContinuous_iff.mp hu η hη
  refine ⟨d/2,half_pos hd,?_⟩
  intro z
  apply (convex_closedBall z (d/2)).lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => hψ.differentiable (by norm_num) x)
  intro x hx
  have hdist : dist x z<d := lt_of_le_of_lt hx (half_lt_self hd)
  have hdiff := hclose hdist
  change ‖fderiv ℝ ψ x‖≤‖fderiv ℝ ψ z‖+η
  exact norm_le_norm_add_const_of_dist_le hdiff.le

end RegularPointCoordinates

end

end OAI
