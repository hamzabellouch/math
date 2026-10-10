import OAI.Geometry.RCD.Transport.RenyiPlanVariation

namespace OAI

/-! # The actual Sobolev primitive for finite Rényi first variations -/

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates

def renyiDualClip (ε q r : ℝ) : ℝ :=
  renyiDualPower q (max r ε)-renyiDualPower q ε

theorem renyiDualClip_zero {ε : ℝ} (hε : 0<ε) (q : ℝ) : renyiDualClip ε q 0=0 := by
  simp only [renyiDualClip,max_eq_right hε.le,sub_self]

theorem renyiDualClip_lipschitz {ε q : ℝ} (hε : 0<ε) (hq0 : 0<q) (hq1 : q<1) :
    LipschitzWith ⟨|q-1| * ε^(q-1),by positivity⟩ (renyiDualClip ε q) := by
  have hd (r : ℝ) (hr : r∈Ici ε) :
      HasDerivWithinAt (renyiDualPower q) ((q-1)*r^(q-1)) (Ici ε) r :=
    (renyiDualPower_hasDerivAt hq0.ne' (hε.trans_le hr)).hasDerivWithinAt
  have hb (r : ℝ) (hr : r∈Ici ε) : ‖(q-1)*r^(q-1)‖≤|q-1| * ε^(q-1) := by
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.rpow_nonneg (hε.le.trans hr) _)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hε hr (by linarith)) (abs_nonneg _)
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Ici ε)
    (show max b ε∈Ici ε from le_max_right b ε) (show max a ε∈Ici ε from le_max_right a ε)
  have hm := (LipschitzWith.id.max_const ε).dist_le_mul a b
  simp only [id_eq,NNReal.coe_one,one_mul] at hm
  calc
    dist (renyiDualClip ε q a) (renyiDualClip ε q b) =
        |renyiDualPower q (max a ε)-renyiDualPower q (max b ε)| := by
      simp only [Real.dist_eq,renyiDualClip,sub_sub_sub_cancel_right]
    _ ≤ (|q-1| * ε^(q-1))*dist (max a ε) (max b ε) := by
      simpa only [Real.norm_eq_abs,Real.dist_eq] using h
    _ ≤ (|q-1| * ε^(q-1))*dist a b :=
      mul_le_mul_of_nonneg_left hm (by positivity)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

def SobolevSpace.renyiDual (ρ : SobolevSpace μ hQ) {ε q : ℝ}
    (hε : 0<ε) (hq0 : 0<q) (hq1 : q<1) : SobolevSpace μ hQ :=
  SobolevSpace.comp μ hQ (renyiDualClip_lipschitz hε hq0 hq1) (renyiDualClip_zero hε q) ρ

omit [BorelSpace X] in
theorem SobolevSpace.renyiDual_coe (ρ : SobolevSpace μ hQ) {ε q : ℝ}
    (hε : 0<ε) (hq0 : 0<q) (hq1 : q<1)
    (hl : ∀ᵐ x ∂μ, ε≤SobolevSpace.toLp μ hQ ρ x) :
    SobolevSpace.toLp μ hQ (ρ.renyiDual μ hQ hε hq0 hq1) =ᵐ[μ]
      fun x => renyiDualPower q (SobolevSpace.toLp μ hQ ρ x)-renyiDualPower q ε := by
  filter_upwards [SobolevSpace.comp_coe μ hQ
    (renyiDualClip_lipschitz hε hq0 hq1) (renyiDualClip_zero hε q) ρ,hl] with x hx hxl
  simpa only [SobolevSpace.renyiDual,Function.comp_apply,renyiDualClip,max_eq_left hxl] using hx

attribute [local instance] pathBorel pathBorelSpace

omit hQ [MeasurableSpace X] [BorelSpace X] in
theorem planInitialSecant_sub_const (π : Measure C(Time,X)) (f : X → ℝ) (c t : ℝ) :
    planInitialSecant π (fun x => f x-c) t=planInitialSecant π f t := by
  unfold planInitialSecant
  congr 1
  apply integral_congr_ae
  filter_upwards with γ
  ring

variable [ProperSpace X] [IsFiniteMeasure μ] [μ.Regular]

/-- The finite power first variation is the energy pairing with the
constructed Sobolev primitive. No derivative of a density representative
is used on exceptional sets. -/
theorem reference_renyi_signed_variation
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C≠∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1)≤D)
    (u ρ : SobolevSpace μ hQ) {ε q : ℝ} (hε : 0<ε) (hq0 : 0<q) (hq1 : q<1)
    (hl : ∀ᵐ x ∂μ, ε≤SobolevSpace.toLp μ hQ ρ x)
    (h0 : π.map (fun γ => γ 0)=μ.withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hQ ρ x)))
    {φ ψ : X → ℝ} (hu : φ=ᵐ[μ] SobolevSpace.toLp μ hQ u)
    (had : ∀ x y, φ x+ψ y≤dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1)=dist (γ 0) (γ 1)^2/2)
    (hb : ∀ᵐ γ ∂π, SobolevSpace.minimalSlope μ hQ u (γ 0)≤dist (γ 0) (γ 1)) :
    Tendsto (planInitialSecant π (fun x => (SobolevSpace.toLp μ hQ ρ x)^(q-1)))
      (𝓝[>] (0:ℝ)) (𝓝 (-energyForm μ hQ u (ρ.renyiDual μ hQ hε hq0 hq1))) := by
  let r := SobolevSpace.toLp μ hQ ρ
  let π' := inverseInitialDensityPlan π r
  have hlen := inverseInitialDensityPlan_le μ π hε hl
    (Measure.absolutelyContinuous_of_le_smul (hcomp 0))
  let : IsFiniteMeasure π' := inverseInitialDensityPlan_finite μ π hε hl
    (Measure.absolutelyContinuous_of_le_smul (hcomp 0))
  have hac : π' ≪ π := inverseInitialDensityPlan_ac π r
  have hcomp' := inverseInitialDensityPlan_compression μ π hε hl hcomp
  have hC' : ENNReal.ofReal ε⁻¹*C≠∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC
  have hD' : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π' :=
    hD.of_measure_le_smul ENNReal.ofReal_ne_top hlen
  have hinit : π'.map (fun γ => γ 0)=μ :=
    inverseInitialDensityPlan_initial μ π (Lp.stronglyMeasurable r).measurable
      (hl.mono fun _ hx => hε.trans_le hx) h0
  have hd := kantorovich_signed_first_variation μ hQ π' (hac.ae_le hgeo) hC' hcomp' hD'
    u (ρ.renyiDual μ hQ hε hq0 hq1) hu had (hac.ae_le hc) (hac.ae_le hb)
  rw [hinit,weightedGradientPair_reference] at hd
  have hrep := SobolevSpace.renyiDual_coe μ hQ ρ hε hq0 hq1 hl
  have heq : planInitialSecant π' (fun x => renyiDualPower q (r x)) =ᶠ[𝓝[>] (0:ℝ)]
      planInitialSecant π' (SobolevSpace.toLp μ hQ (ρ.renyiDual μ hQ hε hq0 hq1)) := by
    have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ), t<1 :=
      (gt_mem_nhds (show (0:ℝ)<1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hsmall,self_mem_nhdsWithin] with t ht1 ht0
    have hh := planInitialSecant_congr_ae μ π'
      (fun s => Measure.absolutelyContinuous_of_le_smul (hcomp' s)) hrep ⟨ht0.le,ht1.le⟩
    exact (hh.trans (planInitialSecant_sub_const π' _ (renyiDualPower q ε) t)).symm
  have hd' := hd.congr' heq.symm
  have he := planInitialSecant_renyi_reweight_tendsto μ π hgeo hC hcomp hD hDb
    (SobolevSpace.minimalSlope_isRelaxed μ hQ ρ) hε hl hq0 hq1
  simpa only [π',r,sub_sub_cancel,sub_zero] using hd'.sub he

end RegularPointCoordinates

end

end OAI
