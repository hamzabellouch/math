import OAI.Geometry.RCD.Transport.RenyiPathTails

namespace OAI

/-! # Noncompact Rényi first variation by integrable path truncation -/

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
attribute [local instance] pathBorel pathBorelSpace

/-- Ordinary integrability of the explicit path majorant and weighted
energy density suffices to remove all path truncations. No finite-volume
or global positive lower bound is imposed on the density. -/
theorem renyi_core_signed_variation
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
    {q : ℝ} (hq0 : 0<q) (hq1 : q<1)
    (hTail : Integrable (renyiPathMajorant L q g) π)
    (hEnergy : Integrable (fun x =>
      (q-1)*(SobolevSpace.toLp μ hQ ρ x)^(q-1)*localGamma μ hQ u ρ x) μ) :
    Tendsto (planInitialSecant π (fun x => (SobolevSpace.toLp μ hQ ρ x)^(q-1)))
      (𝓝[>] (0:ℝ)) (𝓝 (-(∫ x,
        (q-1)*(SobolevSpace.toLp μ hQ ρ x)^(q-1)*localGamma μ hQ u ρ x ∂μ))) := by
  let r := SobolevSpace.toLp μ hQ ρ
  let F : X → ℝ := fun x => (q-1)*(r x)^(q-1)*localGamma μ hQ u ρ x
  let π' := inverseInitialDensityPlan π r
  let A : ℕ → Set C(Time,X) := fun n => {γ | |pathLogControl g γ|≤(n:ℝ)}
  have hA (n : ℕ) : MeasurableSet (A n) :=
    measurableSet_le (pathLogControl_measurable hg.continuous.measurable).abs measurable_const
  have hinit : π'.map (fun γ => γ 0)=μ :=
    inverseInitialDensityPlan_initial μ π (Lp.stronglyMeasurable r).measurable hp h0
  have hiF : Integrable F (π'.map (fun γ => γ 0)) := by rw [hinit]; exact hEnergy
  have hip := hiF.comp_measurable (measurable_path_eval 0)
  have hInt : (∫ γ,F (γ 0) ∂π')=∫ x,F x ∂μ := by
    rw [←integral_map (measurable_path_eval 0).aemeasurable hiF.aestronglyMeasurable,hinit]
  apply tendsto_of_uniform_secant_tails
    (fₙ := fun n => planInitialSecant (π.restrict (A n)) (fun x => (r x)^(q-1)))
    (cₙ := fun n => -(∫γ in A n,F (γ 0) ∂π'))
    (eₙ := fun n => ∫γ in (A n)ᶜ,renyiPathMajorant L q g γ ∂π)
  · have ht := tendsto_integral_log_levels π' (pathLogControl_measurable hg.continuous.measurable) hip
    simp only [Function.comp_apply] at ht
    rw [hInt] at ht
    exact ht.neg
  · exact tendsto_integral_compl_log_levels π (pathLogControl_measurable hg.continuous.measurable) hTail
  · exact renyi_core_path_set_variation μ hQ π hgeo hC hcomp hD u ρ hp hg hlog h0 hu had hc hb hq0 hq1
  · intro n
    have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ), t<1/8 :=
      (gt_mem_nhds (by norm_num : (0:ℝ)<1/8)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hsmall,self_mem_nhdsWithin] with t ht1 ht0
    let s : Time := ⟨t,ht0.le,by linarith⟩
    apply planInitialSecant_restrict_error_of_majorant π
      ((Lp.stronglyMeasurable r).measurable.pow_const _) hTail (hA n) s ht0
    have he (a : Time) : ∀ᵐ γ ∂π, (r (γ a))^(q-1)=Real.exp ((q-1)*g (γ a)) := by
      have hpos := ae_of_ae_map (measurable_path_eval a).aemeasurable
        ((Measure.absolutelyContinuous_of_le_smul (hcomp a)).ae_le hp)
      have hrep := ae_of_ae_map (measurable_path_eval a).aemeasurable
        ((Measure.absolutelyContinuous_of_le_smul (hcomp a)).ae_eq hlog)
      filter_upwards [hpos,hrep] with γ hp' hr
      rw [Real.rpow_def_of_pos hp',hr,mul_comm]
    filter_upwards [he s,he 0,hgeo] with γ hs hzero hγ
    rw [hs,hzero]
    exact renyi_exp_path_increment hg hq1.le hγ s ht1.le

end RegularPointCoordinates

end

end OAI
