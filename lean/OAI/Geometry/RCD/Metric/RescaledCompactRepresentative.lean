import OAI.Geometry.RCD.Sobolev.CompactGradientRepresentative

namespace OAI

/-! # Compact Lipschitz representatives at the original physical scale -/

open Set Filter Metric MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.rescaled_compact_representative {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    (q : SobolevSpace (hausdorff n X) hX.quadratic)
    (p : X) {r c Q : ℝ} (hr : 0<r) (hQ : 0≤Q)
    (hgrad : ∀ᵐ x ∂hausdorff n X,
      r^2*localGamma (hausdorff n X) hX.quadratic q q x≤Q^2)
    (hzero : ∀ᵐ x ∂hausdorff n X, x∉ball p (c*r) →
      SobolevSpace.toLp (hausdorff n X) hX.quadratic q x=0) :
    ∃ v : X → ℝ, LipschitzWith ⟨Q/r,div_nonneg hQ hr.le⟩ v ∧
      HasCompactSupport v ∧ tsupport v⊆closedBall p (c*r) ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic q=ᵐ[hausdorff n X] v := by
  apply hX.compact_lipschitz_of_gradient hn q ⟨Q/r,div_nonneg hQ hr.le⟩ ?_ p (c*r) ?_
  · filter_upwards [hgrad,localGamma_self (hausdorff n X) hX.quadratic q,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg (hausdorff n X) hX.quadratic q)]
      with x hx he hnon
    rw [he,← mul_pow] at hx
    have hh := (sq_le_sq₀ (mul_nonneg hr.le hnon) hQ).mp hx
    exact (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using hh)
  · filter_upwards [hzero] with x hx hd
    exact hx (by simpa only [mem_ball,not_lt,dist_comm] using hd.le)

end RegularPointCoordinates

end

end OAI
