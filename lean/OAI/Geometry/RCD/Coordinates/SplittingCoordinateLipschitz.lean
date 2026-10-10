import OAI.Geometry.RCD.Sobolev.ColumnGradientValueBound

namespace OAI

/-! # Local Lipschitz control of the actual splitting coordinates -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.splitting_coordinate_lipschitz {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {p : X} {R ε : ℝ}
    (hR : 0 < R) (he : 0 ≤ ε)
    {u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic} {v : X → Euclidean n}
    (hsplit : FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (8*R) ε u v) :
    LipschitzOnWith ⟨(n:ℝ)*(1+ε),by positivity⟩ v (ball p R) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  let z := v x-v y
  let L : ℝ≥0 := ⟨(n:ℝ)*(1+ε)*‖z‖,by positivity⟩
  have hg : ∀ᵐ w ∂(hausdorff n X).restrict (ball p (8*R)),
      localGamma (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic u z)
        (sobolevColumnMap (hausdorff n X) hX.quadratic u z) w ≤ (L:ℝ)^2 := by
    have hL : (L:ℝ)=(n:ℝ)*(1+ε)*‖z‖ := rfl
    rw [hL,mul_pow]
    exact hsplit.directional_gradient (hausdorff n X) hX.quadratic z
  have hl := hX.continuous_local_gradient_lipschitz hn
    (sobolevColumnMap (hausdorff n X) hX.quadratic u z) (fun w => ⟪v w,z⟫_ℝ) p hR L
    (hsplit.continuous.inner continuousOn_const)
    (sobolevColumnMap_representative (hausdorff n X) hX.quadratic u _ v hsplit.representative z) hg
  have hh := hl.dist_le_mul x hx y hy
  rw [Real.dist_eq,← inner_sub_left] at hh
  change |⟪z,z⟫_ℝ| ≤ ((n:ℝ)*(1+ε)*‖z‖)*dist x y at hh
  rw [real_inner_self_eq_norm_sq,abs_of_nonneg (sq_nonneg _)] at hh
  change ‖z‖ ≤ (n:ℝ)*(1+ε)*dist x y
  by_cases hz : ‖z‖=0
  · rw [hz]
    positivity
  · have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith only [hh,hzpos]

end RegularPointCoordinates

end

end OAI
