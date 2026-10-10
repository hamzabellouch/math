import OAI.Geometry.RCD.Sobolev.LocalGradientRepresentative
import OAI.Geometry.RCD.Sobolev.DirectionalGradientBound

namespace OAI

/-! # Gradient bounds for a prescribed continuous local representative -/

open Set Metric MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
theorem NoncollapsedRCD.continuous_local_gradient_lipschitz {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (f : SobolevSpace (hausdorff n X) hX.quadratic) (v : X → ℝ)
    (p : X) {R : ℝ} (hR : 0 < R) (L : ℝ≥0)
    (hv : ContinuousOn v (ball p (8*R)))
    (hrep : SobolevSpace.toLp (hausdorff n X) hX.quadratic f =ᵐ[
      (hausdorff n X).restrict (ball p (8*R))] v)
    (hgrad : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*R)),
      localGamma (hausdorff n X) hX.quadratic f f x ≤ (L : ℝ)^2) :
    LipschitzOnWith L v (ball p R) := by
  let μ := hausdorff n X
  let := hX.openPos K n
  have hg : ∀ᵐ x ∂μ.restrict (ball p (8*R)),
      SobolevSpace.minimalSlope μ hX.quadratic f x ≤ L := by
    filter_upwards [hgrad,ae_restrict_of_ae (localGamma_self μ hX.quadratic f)] with x hx he
    rw [he] at hx
    nlinarith [L.coe_nonneg]
  obtain ⟨w,hw,hwrep⟩ := hX.local_lipschitz_representative hn
    (SobolevSpace.minimalSlope_isRelaxed μ hX.quadratic f) L hR hg
  have hs : ball p R ⊆ ball p (8*R) := ball_subset_ball (by linarith)
  have hvrep : SobolevSpace.toLp μ hX.quadratic f =ᵐ[μ.restrict (ball p R)] v :=
    ae_restrict_of_ae_restrict_of_subset hs hrep
  have hwrep' : SobolevSpace.toLp μ hX.quadratic f =ᵐ[μ.restrict (ball p R)] w :=
    ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hwrep
  have heq : Set.EqOn v w (ball p R) := by
    apply Measure.eqOn_open_of_ae_eq (μ := μ) _ isOpen_ball (hv.mono hs) hw.continuous.continuousOn
    exact hvrep.symm.trans hwrep'
  intro x hx y hy
  rw [heq hx,heq hy]
  exact hw x y

omit [ProperSpace X] in
theorem NoncollapsedRCD.continuous_local_gradient_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (f : SobolevSpace (hausdorff n X) hX.quadratic) (v : X → ℝ)
    (p : X) {R : ℝ} (hR : 0 < R) (L : ℝ≥0)
    (hv : ContinuousOn v (ball p (8*R)))
    (hrep : SobolevSpace.toLp (hausdorff n X) hX.quadratic f =ᵐ[
      (hausdorff n X).restrict (ball p (8*R))] v)
    (hgrad : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*R)),
      localGamma (hausdorff n X) hX.quadratic f f x ≤ (L : ℝ)^2) :
    ∀ x ∈ ball p R, |v x-v p| ≤ (L : ℝ)*dist x p := by
  intro x hx
  simpa only [Real.dist_eq] using
    (hX.continuous_local_gradient_lipschitz hn f v p hR L hv hrep hgrad).dist_le_mul
      x hx p (mem_ball_self hR)

end RegularPointCoordinates

end

end OAI
