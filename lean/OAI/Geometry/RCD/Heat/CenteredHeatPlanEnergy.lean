import OAI.Geometry.RCD.Heat.HeatPlanQuadraticEnergy
import OAI.Geometry.RCD.Metric.InwardLocality

namespace OAI

/-! # Constant shifts preserve the exact heat-plan directional energy -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)
attribute [local instance] pathBorel pathBorelSpace

theorem centered_heat_plan_quadratic_energy (a₀ : S) (b₀ : T) (hK : K ≤ 0)
    (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0)) {R : ℝ} (hR : 0 < R)
    (hS : ∀ a : S, dist p a ≤ R) (hT : ∀ b : T, dist p b ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (μ.map Subtype.val) (ν.map Subtype.val)
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • hausdorff n X)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    (s : Time) (hs : 0 < (s:ℝ)) (hs1 : (s:ℝ) < 1)
    (u v : SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u
      =ᵐ[(hausdorff n X).restrict (closedBall p (6*R))] D.forward.potential ((s:ℝ)/2))
    (c : ℝ)
    (hvu : SobolevSpace.toLp (hausdorff n X) hX.quadratic (v-u)
      =ᵐ[(hausdorff n X).restrict (closedBall p (6*R))] fun _ => c) :
    (∫ x in closedBall p (6*R), radialCutoff p (3*R) x*
      localGamma (hausdorff n X) hX.quadratic v v x ∂π.map (fun γ => γ s))
      = 4*∫ γ, dist (γ 0) (γ 1)^2 ∂π := by
  have he := D.heat_plan_quadratic_energy a₀ b₀ hK hε1 hε0 hR hS hT
    π hgeo hopt hC hcomp hD s hs hs1 u hu
  have hΓ := localGamma_self_eq_of_constant_difference (hausdorff n X) hX.quadratic
    (closedBall p (6*R)) v u c hvu
  have hac := Measure.absolutelyContinuous_of_le_smul (hcomp s)
  have heq : (∫ x in closedBall p (6*R), radialCutoff p (3*R) x*
      localGamma (hausdorff n X) hX.quadratic v v x ∂π.map (fun γ => γ s))=
      ∫ x in closedBall p (6*R), radialCutoff p (3*R) x*
      localGamma (hausdorff n X) hX.quadratic u u x ∂π.map (fun γ => γ s) := by
    apply integral_congr_ae
    filter_upwards [(hac.restrict (closedBall p (6*R))).ae_eq hΓ] with x hx
    rw [hx]
  exact heq.trans he

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
