import OAI.Geometry.RCD.Transport.RenyiSmoothDual

namespace OAI

/-! # Localized power first variation with its actual energy density -/

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
attribute [local instance] pathBorel pathBorelSpace

theorem path_renyi_smooth_variation (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C≠∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {D : ℝ} (hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1)≤D)
    (u ρ : SobolevSpace μ hQ) {ε M q : ℝ}
    (hε : 0<ε) (hq0 : 0<q) (hq1 : q<1)
    (hbound : ∀ t : Time, ∀ᵐ γ ∂π,
      ε≤SobolevSpace.toLp μ hQ ρ (γ t) ∧ SobolevSpace.toLp μ hQ ρ (γ t)≤M)
    {φ ψ : X → ℝ} (hu : φ=ᵐ[μ] SobolevSpace.toLp μ hQ u)
    (had : ∀ x y, φ x+ψ y≤dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1)=dist (γ 0) (γ 1)^2/2)
    (hb : ∀ᵐ γ ∂π, SobolevSpace.minimalSlope μ hQ u (γ 0)≤dist (γ 0) (γ 1)) :
    Tendsto (planInitialSecant π (fun x => (SobolevSpace.toLp μ hQ ρ x)^(q-1)))
      (𝓝[>] (0:ℝ)) (𝓝 (-weightedGradientPair μ hQ
        ((inverseInitialDensityPlan π (SobolevSpace.toLp μ hQ ρ)).map (fun γ => γ 0))
        u (ρ.renyiSmooth μ hQ hε hq1.le))) := by
  apply path_renyi_signed_variation μ hQ π hgeo hC hcomp hD hDb u ρ
    (ρ.renyiSmooth μ hQ hε hq1.le) hε hq0 hq1 hbound
    (renyiDualPower q ε-renyiSmoothDual ε q ε) _ hu had hc hb
  intro t
  have hrep := SobolevSpace.comp_coe μ hQ (renyiSmoothDual_lipschitz hε hq1.le)
    (renyiSmoothDual_zero ε q) ρ
  have hr := ae_of_ae_map (measurable_path_eval t).aemeasurable
    ((Measure.absolutelyContinuous_of_le_smul (hcomp t)).ae_eq hrep)
  filter_upwards [hr,hbound t] with γ he hγ
  change SobolevSpace.toLp μ hQ (SobolevSpace.comp μ hQ _ _ ρ) (γ t)=_ at he ⊢
  rw [he]
  exact renyiSmoothDual_formula hε hq0.ne' hγ.1

/-- The finite-dimensional power variation on a bounded path family is
the integral of the genuine carré-du-champ, with the exact density power.
Only the restricted family is bounded; the reference volume may be infinite. -/
theorem renyi_core_path_set_variation
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C≠∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    (u ρ : SobolevSpace μ hQ)
    (hp : ∀ᵐ x ∂μ, 0<SobolevSpace.toLp μ hQ ρ x)
    {g : X → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (hlog : (fun x => Real.log (SobolevSpace.toLp μ hQ ρ x)) =ᵐ[μ] g)
    (h0 : π.map (fun γ => γ 0)=μ.withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hQ ρ x)))
    {φ ψ : X → ℝ} (hu : φ=ᵐ[μ] SobolevSpace.toLp μ hQ u)
    (had : ∀ x y, φ x+ψ y≤dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1)=dist (γ 0) (γ 1)^2/2)
    (hb : ∀ᵐ γ ∂π, SobolevSpace.minimalSlope μ hQ u (γ 0)≤dist (γ 0) (γ 1))
    {q : ℝ} (hq0 : 0<q) (hq1 : q<1) (n : ℕ) :
    Tendsto (planInitialSecant (π.restrict {γ | |pathLogControl g γ|≤(n:ℝ)})
      (fun x => (SobolevSpace.toLp μ hQ ρ x)^(q-1))) (𝓝[>] (0:ℝ))
      (𝓝 (-(∫ γ in {γ | |pathLogControl g γ|≤(n:ℝ)},
        (q-1)*(SobolevSpace.toLp μ hQ ρ (γ 0))^(q-1)*localGamma μ hQ u ρ (γ 0)
          ∂inverseInitialDensityPlan π (SobolevSpace.toLp μ hQ ρ)))) := by
  let A : Set C(Time,X) := {γ | |pathLogControl g γ|≤(n:ℝ)}
  let σ := π.restrict A
  let r := SobolevSpace.toLp μ hQ ρ
  let B : ℝ := (n:ℝ)+(L:ℝ)*(n:ℝ)
  let ε : ℝ := Real.exp (-B)
  have hε : 0<ε := Real.exp_pos _
  have hA : MeasurableSet A :=
    measurableSet_le (pathLogControl_measurable hg.continuous.measurable).abs measurable_const
  have hm : ∀ᵐ γ ∂σ, |g (γ 0)|≤(n:ℝ) ∧ dist (γ 0) (γ 1)≤(n:ℝ) :=
    (ae_restrict_mem hA).mono fun _ hn => pathLogControl_bound hn
  have hσ (s : Time) : σ.map (fun γ => γ s)≤C • μ := restrict_plan_compression μ π hcomp A s
  have hrep (s : Time) : ∀ᵐ γ ∂σ, Real.log (r (γ s))=g (γ s) :=
    ae_of_ae_map (measurable_path_eval s).aemeasurable
      ((Measure.absolutelyContinuous_of_le_smul (hσ s)).ae_eq hlog)
  have hpos (s : Time) : ∀ᵐ γ ∂σ, 0<r (γ s) :=
    ae_of_ae_map (measurable_path_eval s).aemeasurable
      ((Measure.absolutelyContinuous_of_le_smul (hσ s)).ae_le hp)
  have hbound (s : Time) : ∀ᵐ γ ∂σ, ε≤r (γ s) ∧ r (γ s)≤Real.exp B := by
    filter_upwards [hm,ae_restrict_of_ae hgeo,hrep s,hpos s] with γ hn hγ hr hp'
    have hi := lipschitz_geodesic_increment hg hγ s
    have ht : (L:ℝ)*(s:ℝ)*dist (γ 0) (γ 1)≤(L:ℝ)*(n:ℝ) := by
      calc
        _ ≤ (L:ℝ)*1*dist (γ 0) (γ 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left s.property.2 L.coe_nonneg) dist_nonneg
        _ ≤ (L:ℝ)*1*(n:ℝ) := mul_le_mul_of_nonneg_left hn.2 (by positivity)
        _ = _ := by ring
    have ha := abs_add_le (g (γ s)-g (γ 0)) (g (γ 0))
    simp only [sub_add_cancel] at ha
    have hb' : |g (γ s)|≤B := by dsimp only [B]; linarith [hn.1]
    rw [←Real.exp_log hp',hr]
    exact ⟨Real.exp_le_exp.mpr (abs_le.mp hb').1,Real.exp_le_exp.mpr (abs_le.mp hb').2⟩
  have hd := path_renyi_smooth_variation μ hQ σ (ae_restrict_of_ae hgeo) hC hσ
    (hD.mono_measure Measure.restrict_le_self) (hm.mono fun _ hh => hh.2)
    u ρ hε hq0 hq1 hbound hu had (ae_restrict_of_ae hc) (ae_restrict_of_ae hb)
  have hinit := inverseInitialDensityPlan_initial μ π (Lp.stronglyMeasurable r).measurable hp h0
  have hν : (inverseInitialDensityPlan σ r).map (fun γ => γ 0)≤(1:ℝ≥0∞) • μ := by
    rw [inverseInitialDensityPlan_restrict π r hA,one_smul]
    exact (Measure.map_mono Measure.restrict_le_self (measurable_path_eval 0)).trans_eq hinit
  rw [weightedGradientPair_eq_bracket μ hQ (C := 1) (by norm_num) hν,
    ←integral_localGamma μ hQ (C := 1) (by norm_num) hν] at hd
  have hΓ : Measurable (localGamma μ hQ u (ρ.renyiSmooth μ hQ hε hq1.le)) := by
    unfold localGamma
    fun_prop
  rw [integral_map (measurable_path_eval 0).aemeasurable hΓ.aestronglyMeasurable] at hd
  have heq : (∫ γ, localGamma μ hQ u (ρ.renyiSmooth μ hQ hε hq1.le) (γ 0)
      ∂inverseInitialDensityPlan σ r)=
      ∫ γ, (q-1)*r (γ 0)^(q-1)*localGamma μ hQ u ρ (γ 0)
        ∂inverseInitialDensityPlan σ r := by
    apply integral_congr_ae
    have hrΓ := ae_of_ae_map (measurable_path_eval 0).aemeasurable
      ((Measure.absolutelyContinuous_of_le_smul hν).ae_eq
        (localGamma_renyiSmooth μ hQ u ρ hε hq1.le))
    filter_upwards [hrΓ,(inverseInitialDensityPlan_ac σ r).ae_le (hbound 0)] with γ hγ hr
    change localGamma μ hQ u (ρ.renyiSmooth μ hQ hε hq1.le) (γ 0)=
      renyiSmoothSlope ε q (r (γ 0))*localGamma μ hQ u ρ (γ 0) at hγ
    simpa only [renyiSmoothSlope,max_eq_left hr.1] using hγ
  rw [heq,inverseInitialDensityPlan_restrict π r hA] at hd
  exact hd

end RegularPointCoordinates

end

end OAI
