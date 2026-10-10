import OAI.Geometry.RCD.Transport.RenyiPathVariation
import OAI.Geometry.RCD.Transport.RenyiSobolev

namespace OAI

/-! # Finite Rényi first variations on a localized path family -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X)
attribute [local instance] pathBorel pathBorelSpace

theorem renyi_path_integrable_of_bounds (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (ρ : Lp ℝ 2 μ) {ε M q : ℝ} (hε : 0<ε) (hq0 : 0<q) (hq1 : q<1)
    (hb : ∀ t : Time, ∀ᵐ γ ∂π, ε≤ρ (γ t) ∧ ρ (γ t)≤M) (t : Time) :
    Integrable (fun γ : C(Time,X) => renyiDualPower q (ρ (γ t))) π ∧
    Integrable (fun γ : C(Time,X) => (ρ (γ t))^(q-1)) π := by
  have hm := (Lp.stronglyMeasurable ρ).measurable.comp (measurable_path_eval t)
  constructor
  · apply Integrable.of_bound ((hm.pow_const q).const_mul _).aestronglyMeasurable
      (|(q-1)/q| * M^q)
    filter_upwards [hb t] with γ hγ
    change ‖(q-1)/q*(ρ (γ t))^q‖ ≤ _
    rw [Real.norm_eq_abs,abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (hε.le.trans hγ.1) _)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hε.le.trans hγ.1) hγ.2 hq0.le) (abs_nonneg _)
  · apply Integrable.of_bound (hm.pow_const (q-1)).aestronglyMeasurable (ε^(q-1))
    filter_upwards [hb t] with γ hγ
    change ‖(ρ (γ t))^(q-1)‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (hε.le.trans hγ.1) _)]
    exact Real.rpow_le_rpow_of_nonpos hε hγ.1 (by linarith)

theorem inverseInitialDensityPlan_compression_path (π : Measure C(Time,X))
    {ρ : X → ℝ} {ε : ℝ} (hε : 0<ε) (hl : ∀ᵐ γ ∂π, ε≤ρ (γ 0))
    {C : ℝ≥0∞} (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • μ) (t : Time) :
    (inverseInitialDensityPlan π ρ).map (fun γ => γ t)≤(ENNReal.ofReal ε⁻¹*C) • μ := by
  have hh := Measure.map_mono (inverseInitialDensityPlan_le_path π hε hl) (measurable_path_eval t)
  rw [Measure.map_smul _ (measurable_path_eval t).aemeasurable] at hh
  apply hh.trans
  intro s
  simpa only [Measure.smul_apply,smul_eq_mul,mul_assoc,mul_comm,mul_left_comm] using
    mul_le_mul_left (hcomp t s) (ENNReal.ofReal ε⁻¹)

variable [ProperSpace X] [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

/-- The local family requires bounded density only along its own paths.
The represented primitive is the genuine Sobolev direction in the
Kantorovich first variation. -/
theorem path_renyi_signed_variation (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C≠∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1)≤D)
    (u ρ v : SobolevSpace μ hQ) {ε M q : ℝ}
    (hε : 0<ε) (hq0 : 0<q) (hq1 : q<1)
    (hbound : ∀ t : Time, ∀ᵐ γ ∂π,
      ε≤SobolevSpace.toLp μ hQ ρ (γ t) ∧ SobolevSpace.toLp μ hQ ρ (γ t)≤M)
    (c : ℝ)
    (hv : ∀ t : Time, ∀ᵐ γ ∂π, SobolevSpace.toLp μ hQ v (γ t) =
      renyiDualPower q (SobolevSpace.toLp μ hQ ρ (γ t))-c)
    {φ ψ : X → ℝ} (hu : φ=ᵐ[μ] SobolevSpace.toLp μ hQ u)
    (had : ∀ x y, φ x+ψ y≤dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1)=dist (γ 0) (γ 1)^2/2)
    (hb : ∀ᵐ γ ∂π, SobolevSpace.minimalSlope μ hQ u (γ 0)≤dist (γ 0) (γ 1)) :
    Tendsto (planInitialSecant π (fun x => (SobolevSpace.toLp μ hQ ρ x)^(q-1)))
      (𝓝[>] (0:ℝ)) (𝓝 (-weightedGradientPair μ hQ
        ((inverseInitialDensityPlan π (SobolevSpace.toLp μ hQ ρ)).map (fun γ => γ 0)) u v)) := by
  let r := SobolevSpace.toLp μ hQ ρ
  let π' := inverseInitialDensityPlan π r
  have hl (t : Time) : ∀ᵐ γ ∂π, ε≤r (γ t) := (hbound t).mono fun _ hx => hx.1
  have hlen := inverseInitialDensityPlan_le_path π hε (hl 0)
  let : IsFiniteMeasure (ENNReal.ofReal ε⁻¹ • π) := Measure.smul_finite _ ENNReal.ofReal_ne_top
  let : IsFiniteMeasure π' := isFiniteMeasure_of_le _ hlen
  have hac : π' ≪ π := inverseInitialDensityPlan_ac π r
  have hcomp' := inverseInitialDensityPlan_compression_path μ π hε (hl 0) hcomp
  have hC' : ENNReal.ofReal ε⁻¹*C≠∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC
  have hD' := hD.of_measure_le_smul ENNReal.ofReal_ne_top hlen
  have hd := kantorovich_signed_first_variation μ hQ π' (hac.ae_le hgeo) hC' hcomp' hD'
    u v hu had (hac.ae_le hc) (hac.ae_le hb)
  have heq : planInitialSecant π' (fun x => renyiDualPower q (r x)) =ᶠ[𝓝[>] (0:ℝ)]
      planInitialSecant π' (SobolevSpace.toLp μ hQ v) := by
    have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ), t<1 :=
      (gt_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
    filter_upwards [hsmall,self_mem_nhdsWithin] with t ht1 ht0
    unfold planInitialSecant
    congr 1
    apply integral_congr_ae
    filter_upwards [hac.ae_le (hv ⟨t,ht0.le,ht1.le⟩),hac.ae_le (hv 0)] with γ hvt hv0
    rw [show geodesicExtension γ t=γ ⟨t,ht0.le,ht1.le⟩ from
      geodesicExtension_eq γ ⟨t,ht0.le,ht1.le⟩]
    simp only [hvt,hv0]
    dsimp only [r]
    ring
  have hd' := hd.congr' heq.symm
  have hi := renyi_path_integrable_of_bounds μ π r hε hq0 hq1 hbound
  have he := planInitialSecant_renyi_reweight_tendsto_path μ π hgeo hC hcomp hD hDb
    (SobolevSpace.minimalSlope_isRelaxed μ hQ ρ) hε hl hq0 hq1
    (fun t => (hi t).1) (fun t => (hi t).2)
  simpa only [π',r,sub_sub_cancel,sub_zero] using hd'.sub he

end RegularPointCoordinates

end

end OAI
