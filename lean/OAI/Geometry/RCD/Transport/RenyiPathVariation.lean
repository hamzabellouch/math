import OAI.Geometry.RCD.Transport.RenyiPlanVariation

namespace OAI

/-! # Localized finite Rényi variations without finite reference volume

Only the restricted path family needs a positive lower density bound.
This is suitable for the density-level and displacement truncations used
on the noncompact RCD space.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X)
attribute [local instance] pathBorel pathBorelSpace

theorem planInitialSecant_renyi_reweight_error_path
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C≠∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1)≤D)
    {ρ G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ ρ G)
    {ε q : ℝ} (hε : 0<ε) (hlp : ∀ s : Time, ∀ᵐ γ ∂π, ε≤ρ (γ s)) (hq0 : 0<q) (hq1 : q<1)
    (hif : ∀ s : Time, Integrable (fun γ : C(Time,X) => renyiDualPower q (ρ (γ s))) π)
    (hig : ∀ s : Time, Integrable (fun γ : C(Time,X) => (ρ (γ s))^(q-1)) π)
    (t : Time) (ht : 0<(t:ℝ)) :
    |planInitialSecant (inverseInitialDensityPlan π ρ) (fun x => renyiDualPower q (ρ x)) t-
        planInitialSecant π (fun x => (ρ x)^(q-1)) t| ≤
      (t:ℝ)*((|q-1|/ε*ε^(q-2))*D^2*(C.toReal*∫ x, (G x)^2 ∂μ)) := by
  have hiq : Integrable (fun γ : C(Time,X) =>
      (renyiDualPower q (ρ (γ t))-renyiDualPower q (ρ (γ 0)))/ρ (γ 0)) π := by
    simp_rw [div_eq_mul_inv]
    apply ((hif t).sub (hif 0)).mul_bdd
    · exact ((Lp.stronglyMeasurable ρ).measurable.comp (measurable_path_eval 0)).inv.aestronglyMeasurable
    · filter_upwards [hlp 0] with γ hγ
      rw [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (hε.le.trans hγ))]
      exact inv_anti₀ hε hγ
  have higs : Integrable (fun γ : C(Time,X) => (ρ (γ t))^(q-1)-(ρ (γ 0))^(q-1)) π :=
    (hig t).sub (hig 0)
  have hirem := hiq.sub higs
  have hisq := ((compressionPullback_memLp μ π _ (measurable_path_eval t) hC (hcomp t) ρ).sub
    (compressionPullback_memLp μ π _ (measurable_path_eval 0) hC (hcomp 0) ρ)).integrable_sq
  have hrem : |∫ γ : C(Time,X),
      (renyiDualPower q (ρ (γ t))-renyiDualPower q (ρ (γ 0)))/ρ (γ 0)-
        ((ρ (γ t))^(q-1)-(ρ (γ 0))^(q-1)) ∂π| ≤
      (|q-1|/ε*ε^(q-2))*∫ γ : C(Time,X), (ρ (γ t)-ρ (γ 0))^2 ∂π := by
    apply (abs_integral_le_integral_abs).trans
    rw [←integral_const_mul]
    apply integral_mono_ae hirem.abs (hisq.const_mul _)
    filter_upwards [hlp t,hlp 0] with γ ht h0
    exact renyi_reweight_remainder hε h0 ht hq0 hq1
  have hsq := hG.testPlan_integrated_square μ π hgeo hC hcomp hD hDb t
  have hcoef : 0≤|q-1|/ε*ε^(q-2) := by positivity
  have htotal := hrem.trans (mul_le_mul_of_nonneg_left hsq hcoef)
  simp_rw [planInitialSecant,geodesicExtension_eq]
  rw [inverseInitialDensityPlan_integral π (Lp.stronglyMeasurable ρ).measurable
    ((hlp 0).mono fun _ hh => hε.le.trans hh),←sub_div,
    ←integral_sub hiq higs,abs_div,abs_of_pos ht]
  apply (div_le_iff₀ ht).mpr
  convert htotal using 1; ring

theorem planInitialSecant_renyi_reweight_tendsto_path
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C≠∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1)≤D)
    {ρ G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ ρ G)
    {ε q : ℝ} (hε : 0<ε) (hlp : ∀ s : Time, ∀ᵐ γ ∂π, ε≤ρ (γ s)) (hq0 : 0<q) (hq1 : q<1)
    (hif : ∀ s : Time, Integrable (fun γ : C(Time,X) => renyiDualPower q (ρ (γ s))) π)
    (hig : ∀ s : Time, Integrable (fun γ : C(Time,X) => (ρ (γ s))^(q-1)) π) :
    Tendsto (fun t =>
      planInitialSecant (inverseInitialDensityPlan π ρ) (fun x => renyiDualPower q (ρ x)) t-
        planInitialSecant π (fun x => (ρ x)^(q-1)) t) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun t : ℝ =>
    t*((|q-1|/ε*ε^(q-2))*D^2*(C.toReal*∫ x, (G x)^2 ∂μ)))
  · have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ), t<1 :=
      (gt_mem_nhds (show (0:ℝ)<1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hsmall,self_mem_nhdsWithin] with t ht1 ht0
    exact planInitialSecant_renyi_reweight_error_path μ π hgeo hC hcomp hD hDb hG hε hlp hq0 hq1 hif hig
      ⟨t,ht0.le,ht1.le⟩ ht0
  · simpa using ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).mono_left
      nhdsWithin_le_nhds).mul_const ((|q-1|/ε*ε^(q-2))*D^2*(C.toReal*∫ x, (G x)^2 ∂μ))

end RegularPointCoordinates

end

end OAI
