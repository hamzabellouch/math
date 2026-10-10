import OAI.Geometry.RCD.Transport.PlanGradientMean

namespace OAI

/-! # Local mean endpoint control from a bounded relaxed gradient -/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular]
attribute [local instance] pathBorel pathBorelSpace

/-- A bounded-compression geodesic plan reads the actual relaxed gradient
as an upper gradient, without a compression factor in the final bound. -/
theorem IsRelaxedSlope.testPlan_mean_increment_on
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {D L : ℝ} (hL : 0 ≤ L) (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ D)
    {Ω : Set X} (hstay : ∀ t : Time, ∀ᵐ x ∂π.map (fun γ => γ t), x ∈ Ω)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G)
    (hGb : ∀ᵐ x ∂μ.restrict Ω, G x ≤ L) :
    (∫ γ : C(Time,X), |u (γ 1)-u (γ 0)| ∂π) ≤ D*L := by
  have hflux (r : ℝ) : (∫ γ : C(Time,X), dist (γ 0) (γ 1)*G (geodesicExtension γ r) ∂π) ≤ D*L := by
    let t := Set.projIcc 0 1 zero_le_one r
    have hgb : ∀ᵐ γ ∂π, G (γ t) ≤ L := ae_of_ae_map (measurable_path_eval t).aemeasurable
      ((Measure.absolutelyContinuous_of_le_smul
        ((compression_iff_localized μ _ (hstay t) C).mp (hcomp t))).ae_le hGb)
    have hi : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)*G (γ t)) π :=
      hD.integrable_mul (compressionPullback_memLp μ π _ (measurable_path_eval t) hC (hcomp t) G)
    calc
      _ ≤ ∫ _γ : C(Time,X), D*L ∂π := by
        apply integral_mono_ae hi (integrable_const _)
        filter_upwards [hgb,hDb] with γ hg hd
        exact (mul_le_mul_of_nonneg_left hg dist_nonneg).trans
          (mul_le_mul_of_nonneg_right hd hL)
      _ = _ := by simp
  have hh := hG.testPlan_integrated_subinterval μ π hgeo hC hcomp hD 1
  have hI : IntervalIntegrable (fun r => ∫ γ : C(Time,X),
      dist (γ 0) (γ 1)*G (geodesicExtension γ r) ∂π) volume 0 1 :=
    (testPlan_flux_continuous μ π hgeo hC hcomp hD G).intervalIntegrable 0 1
  have hupper : (∫ r in (0:ℝ)..1, ∫ γ : C(Time,X),
      dist (γ 0) (γ 1)*G (geodesicExtension γ r) ∂π) ≤ D*L := by
    calc
      _ ≤ ∫ _r in (0:ℝ)..1, D*L :=
        intervalIntegral.integral_mono_on zero_le_one hI intervalIntegrable_const (fun r _ => hflux r)
      _ = _ := by simp
  exact hh.trans hupper

end RegularPointCoordinates

end

end OAI
