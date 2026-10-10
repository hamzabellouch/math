import OAI.Geometry.RCD.Transport.RenyiReweight
import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Power-entropy transport reweighting

The finite-dimensional power and its matching primitive have the same
initial variation after changing the initial marginal to the reference
measure. The error is controlled by the actual test-plan square estimate.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem memLp_renyi_negative_power (ρ : Lp ℝ 2 μ) {ε q : ℝ}
    (hε : 0<ε) (hl : ∀ᵐ x ∂μ, ε≤ρ x) (hq : q<1) :
    MemLp (fun x => (ρ x)^(q-1)) 2 μ := by
  apply (memLp_const (ε^(q-1))).mono'
    ((Lp.stronglyMeasurable ρ).measurable.pow_const _).aestronglyMeasurable
  filter_upwards [hl] with x hx
  simp only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (hε.le.trans hx) _)]
  exact Real.rpow_le_rpow_of_nonpos hε hx (by linarith)

theorem memLp_renyiDualPower (ρ : Lp ℝ 2 μ) (hρ : 0≤ρ) {q : ℝ}
    (hq0 : 0<q) (hq1 : q<1) : MemLp (fun x => renyiDualPower q (ρ x)) 2 μ := by
  have hm := ((Lp.memLp ρ).add (memLp_const (1:ℝ))).const_mul |(q-1)/q|
  apply hm.mono'
    (((Lp.stronglyMeasurable ρ).measurable.pow_const q).const_mul _).aestronglyMeasurable
  filter_upwards [(Lp.coeFn_nonneg _).mpr hρ] with x hx
  change 0≤ρ x at hx
  have hb : (ρ x)^q≤ρ x+1 := by
    by_cases h1 : ρ x≤1
    · exact (Real.rpow_le_one hx h1 hq0.le).trans (by linarith)
    · have hh := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h1) hq1.le
      rw [Real.rpow_one] at hh
      linarith
  change ‖renyiDualPower q (ρ x)‖ ≤ |(q-1)/q| * (ρ x+1)
  rw [renyiDualPower,Real.norm_eq_abs,abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hx _)]
  exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)

variable [MetricSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem planInitialSecant_renyi_reweight_error
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C≠∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1)≤D)
    {ρ G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ ρ G)
    {ε q : ℝ} (hε : 0<ε) (hl : ∀ᵐ x ∂μ, ε≤ρ x) (hq0 : 0<q) (hq1 : q<1)
    (t : Time) (ht : 0<(t:ℝ)) :
    |planInitialSecant (inverseInitialDensityPlan π ρ) (fun x => renyiDualPower q (ρ x)) t-
        planInitialSecant π (fun x => (ρ x)^(q-1)) t| ≤
      (t:ℝ)*((|q-1|/ε*ε^(q-2))*D^2*(C.toReal*∫ x, (G x)^2 ∂μ)) := by
  have hlp (s : Time) : ∀ᵐ γ ∂π, ε≤ρ (γ s) :=
    ae_of_ae_map (measurable_path_eval s).aemeasurable
      ((Measure.absolutelyContinuous_of_le_smul (hcomp s)).ae_le hl)
  have hρ : 0≤ρ := (Lp.coeFn_nonneg _).mp (hl.mono fun _ hx => hε.le.trans hx)
  have hf := memLp_renyiDualPower μ ρ hρ hq0 hq1
  have hg := memLp_renyi_negative_power μ ρ hε hl hq1
  have hif (s : Time) : Integrable (fun γ : C(Time,X) => renyiDualPower q (ρ (γ s))) π :=
    ((hf.of_measure_le_smul hC (hcomp s)).comp_of_map
      (measurable_path_eval s).aemeasurable).integrable (by norm_num)
  have hig (s : Time) : Integrable (fun γ : C(Time,X) => (ρ (γ s))^(q-1)) π :=
    ((hg.of_measure_le_smul hC (hcomp s)).comp_of_map
      (measurable_path_eval s).aemeasurable).integrable (by norm_num)
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

theorem planInitialSecant_renyi_reweight_tendsto
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C≠∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1)≤D)
    {ρ G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ ρ G)
    {ε q : ℝ} (hε : 0<ε) (hl : ∀ᵐ x ∂μ, ε≤ρ x) (hq0 : 0<q) (hq1 : q<1) :
    Tendsto (fun t =>
      planInitialSecant (inverseInitialDensityPlan π ρ) (fun x => renyiDualPower q (ρ x)) t-
        planInitialSecant π (fun x => (ρ x)^(q-1)) t) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun t : ℝ =>
    t*((|q-1|/ε*ε^(q-2))*D^2*(C.toReal*∫ x, (G x)^2 ∂μ)))
  · have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ), t<1 :=
      (gt_mem_nhds (show (0:ℝ)<1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hsmall,self_mem_nhdsWithin] with t ht1 ht0
    exact planInitialSecant_renyi_reweight_error μ π hgeo hC hcomp hD hDb hG hε hl hq0 hq1
      ⟨t,ht0.le,ht1.le⟩ ht0
  · simpa using ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).mono_left
      nhdsWithin_le_nhds).mul_const ((|q-1|/ε*ε^(q-2))*D^2*(C.toReal*∫ x, (G x)^2 ∂μ))

end RegularPointCoordinates

end

end OAI
