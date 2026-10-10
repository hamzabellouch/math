import OAI.Geometry.RCD.Metric.InwardLocality
import OAI.Analysis.RCDHeat.HeatFisher

namespace OAI

/-! # Exact energy transfer through a radial cutoff and constant gauge

Tests supported on the inner ball see the original energy, independently
of the outer radial realization and the chosen additive constant.
-/

open Set Filter MeasureTheory Metric
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem cutoff_gauge_weighted_energy (z : X) {r : ℝ} (hr : 0 < r)
    (u w : SobolevSpace μ Q) (F : X → ℝ) (c : ℝ)
    (hu : SobolevSpace.toLp μ Q u =ᵐ[μ] fun x => radialCutoff z r x*(F x-c))
    (hw : SobolevSpace.toLp μ Q w =ᵐ[μ.restrict (closedBall z r)] F)
    (η : X → ℝ) (hη : ∀ᵐ x ∂μ, x ∉ closedBall z r → η x = 0) :
    weightedGamma μ Q η u u = ∫ x in closedBall z r, η x*localGamma μ Q w w x ∂μ := by
  have hdiff : SobolevSpace.toLp μ Q (u-w) =ᵐ[μ.restrict (closedBall z r)] fun _ => -c := by
    rw [map_sub]
    filter_upwards [ae_restrict_of_ae hu,hw,
      ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ Q u) (SobolevSpace.toLp μ Q w)),
      ae_restrict_mem measurableSet_closedBall] with x hux hwx hs hx
    rw [hs]
    change SobolevSpace.toLp μ Q u x-SobolevSpace.toLp μ Q w x = -c
    rw [hux,hwx,radialCutoff_eq_one z hr (mem_closedBall'.mp hx),one_mul]
    ring
  have hg := localGamma_self_eq_of_constant_difference μ Q (closedBall z r) u w (-c) hdiff
  have hz : ∀ᵐ x ∂μ, x ∉ closedBall z r → η x*localGamma μ Q u u x = 0 := by
    filter_upwards [hη] with x hx hout
    rw [hx hout,zero_mul]
  change (∫ x, η x*localGamma μ Q u u x ∂μ) = _
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero hz]
  apply integral_congr_ae
  filter_upwards [hg] with x hx
  rw [hx]

end RegularPointCoordinates

end

end OAI
