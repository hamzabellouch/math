import OAI.Geometry.RCD.Metric.InwardDistance
import OAI.Analysis.RCDHeat.SobolevTestPlan

namespace OAI

/-! # Recovering slope one from a compressed radial plan

An actual radial plan realizes the full metric speed of the distance
function. The weak-upper-gradient inequality then forces slope one at
its initial marginal. This isolates the analytic step from constructing
the radial plan by concentration of its final endpoint.
-/

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular]
attribute [local instance] pathBorel pathBorelSpace

theorem IsRelaxedSlope.integral_speed_le_of_radial_plan
    (π : Measure C(Time, X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)) 2 π)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G)
    (hradial : ∀ t : Time, ∀ᵐ γ ∂π,
      |u (γ t) - u (γ 0)| = (t : ℝ) * dist (γ 0) (γ 1)) :
    (∫ γ, dist (γ 0) (γ 1) ∂π) ≤
      ∫ γ, dist (γ 0) (γ 1) * G (γ 0) ∂π := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hb := hG.testPlan_initial_bound μ π hgeo hC hcomp hD hε
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    (gt_mem_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < 1 ∧
      (∫ γ : C(Time, X), |u (geodesicExtension γ t) - u (γ 0)| ∂π) / t <
        (∫ γ, dist (γ 0) (γ 1) * G (γ 0) ∂π) + ε := by
    filter_upwards [self_mem_nhdsWithin, hsmall, hb] with t ht hs hh
    exact ⟨ht, hs, hh⟩
  obtain ⟨t, ht0, ht1, htb⟩ := hev.exists
  let T : Time := ⟨t, ht0.le, ht1.le⟩
  have he : (∫ γ : C(Time, X), |u (geodesicExtension γ t) - u (γ 0)| ∂π) =
      t * ∫ γ, dist (γ 0) (γ 1) ∂π := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hradial T] with γ hγ
    have hge : geodesicExtension γ t = γ T := geodesicExtension_eq γ T
    rw [hge]
    exact hγ
  rw [he, mul_div_cancel_left₀ _ ht0.ne'] at htb
  exact htb.le

theorem IsRelaxedSlope.eq_one_of_radial_plan
    (π : Measure C(Time, X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)) 2 π)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G)
    (hradial : ∀ t : Time, ∀ᵐ γ ∂π,
      |u (γ t) - u (γ 0)| = (t : ℝ) * dist (γ 0) (γ 1))
    (hupper : ∀ᵐ γ ∂π, G (γ 0) ≤ 1)
    (hpositive : ∀ᵐ γ ∂π, 0 < dist (γ 0) (γ 1)) :
    ∀ᵐ γ ∂π, G (γ 0) = 1 := by
  have hflux := hG.integral_speed_le_of_radial_plan μ π hgeo hC hcomp hD hradial
  have hGi : MemLp (fun γ : C(Time, X) => G (γ 0)) 2 π :=
    compressionPullback_memLp μ π _ (measurable_path_eval 0) hC (hcomp 0) G
  have hi := hD.integrable (by norm_num)
  have hip : Integrable (fun γ : C(Time, X) => dist (γ 0) (γ 1) * G (γ 0)) π :=
    hD.integrable_mul hGi
  have hnonneg : ∀ᵐ γ ∂π,
      0 ≤ dist (γ 0) (γ 1) - dist (γ 0) (γ 1) * G (γ 0) := by
    filter_upwards [hupper] with γ hγ
    exact sub_nonneg.mpr (mul_le_of_le_one_right dist_nonneg hγ)
  have hz : (∫ γ, dist (γ 0) (γ 1) - dist (γ 0) (γ 1) * G (γ 0) ∂π) = 0 := by
    apply le_antisymm _ (integral_nonneg_of_ae hnonneg)
    rw [integral_sub hi hip]
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg (hi.sub hip)).mp hz
  filter_upwards [hae, hpositive] with γ hγ hd
  change dist (γ 0) (γ 1) - dist (γ 0) (γ 1) * G (γ 0) = 0 at hγ
  nlinarith

end RegularPointCoordinates

end OAI
