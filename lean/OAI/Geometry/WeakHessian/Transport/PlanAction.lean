import Mathlib
import OAI.Geometry.WeakHessian.Transport.FormAction
import OAI.Geometry.WeakHessian.Entropy.SmoothDensity
import OAI.Geometry.WeakHessian.Transport.PlanIncrement

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma integrable_shifted_time_function {J : Time → ℝ} (hJ : Continuous J)
    (ν : Measure ℝ) [IsFiniteMeasure ν] (s : ℝ) :
    Integrable (fun r => J (clampTime (s-r))) ν := by
  obtain ⟨C,hC⟩ := (isCompact_range hJ.norm).bddAbove
  apply Integrable.of_bound
    ((hJ.comp (continuous_clampTime.comp (continuous_const.sub continuous_id))).aestronglyMeasurable) C
  exact ae_of_all _ fun r => hC ⟨clampTime (s-r),rfl⟩

lemma IsTestPlan.average_density_action (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {B : ℝ≥0} (hB : ∀ t : Time, π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    {u : Time → Lp ℝ 2 m} (hu : StronglyMeasurable u)
    (hun : ∀ t, ∀ᵐ x ∂m, 0 ≤ u t x)
    (hlaw : ∀ t, densityMeasure m (u t) = π.map (fun γ => γ t))
    (hnorm : ∀ t, ‖u t‖^2 ≤ (B : ℝ))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {s : ℝ} {v : Lp ℝ 2 m}
    (hv : HasDerivAt (fun z => ∫ r, u (clampTime (z-r)) ∂ν) v s) :
    FormActionBound m ((∫ r, u (clampTime (s-r)) ∂ν) : Lp ℝ 2 m) v (planKineticCost π) := by
  let w := fun z => ∫ r, u (clampTime (z-r)) ∂ν
  have hw (z : ℝ) := hπ.exists_timeAverageDensity hB hu hun hlaw hnorm ν z
  intro f hf
  have hJ : Continuous (planMoment π (f : X → ℝ)) :=
    hπ.continuous_integral_eval_local hfin hb (by
      intro o R hR
      let : IsFiniteMeasure (m.restrict (Metric.ball o R)) := ⟨by
        simpa only [Measure.restrict_apply_univ] using hfin _ Metric.isBounded_ball⟩
      exact ((Lp.memLp f).mono_measure Measure.restrict_le_self).integrable (by norm_num))
  have hH : Continuous (planGradientEnergy m π (f : X → ℝ)) :=
    (weakGradient_isMinimal hf.2.1.2).1.1.continuous_integral_sq_eval hfin hπ hb
  have hJi (z : ℝ) := integrable_shifted_time_function hJ ν z
  have hHi (z : ℝ) := integrable_shifted_time_function hH ν z
  have hJlaw (t : Time) : planMoment π (f : X → ℝ) t = ⟪f,u t⟫_ℝ := by
    rw [← integral_densityMeasure_L2 _ _ (hun t),hlaw t]
    exact (integral_map (continuous_eval_const t).measurable.aemeasurable
      ((Lp.memLp f).aestronglyMeasurable.mono_ac
        (Measure.absolutelyContinuous_of_le_smul (hB t)))).symm
  have hpair (z : ℝ) : ⟪f,w z⟫_ℝ = ∫ r, planMoment π (f : X → ℝ) (clampTime (z-r)) ∂ν := by
    simp_rw [hJlaw]
    exact ((innerSL ℝ f).integral_comp_comm (integrable_shiftedDensity hu hnorm ν z)).symm
  have henergy : (∫ x, w s x*(weakGradient m f x)^2 ∂m) =
      ∫ r, planGradientEnergy m π (f : X → ℝ) (clampTime (s-r)) ∂ν := by
    rw [← integral_densityMeasure _ _ (hw s).1,(hw s).2.2.2.2.1,
      timeAverageLaw_integral hπ hB hun hlaw ν s hf.2.2.integrable_sq]
    apply integral_congr_ae
    filter_upwards [] with r
    rw [← integral_densityMeasure _ _ (hun _),hlaw]
    exact integral_map (continuous_eval_const (clampTime (s-r))).measurable.aemeasurable
      (hf.2.2.integrable_sq.1.mono_ac (Measure.absolutelyContinuous_of_le_smul (hB _)))
  have hderiv : HasDerivAt (fun z => ⟪f,w z⟫_ℝ) ⟪f,v⟫_ℝ s := by
    simpa using (hasDerivAt_const s f).inner ℝ hv
  have hlimit : Tendsto (fun h : ℝ => (⟪f,w (s+h)⟫_ℝ-⟪f,w s⟫_ℝ)/h)
      (𝓝[>] 0) (𝓝 ⟪f,v⟫_ℝ) := by
    simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using hderiv.tendsto_slope_zero_right
  have hεbound (ε : ℝ) (hε : 0 < ε) :
      ⟪f,v⟫_ℝ ≤ ((∫ r, planGradientEnergy m π (f : X → ℝ) (clampTime (s-r)) ∂ν)+ε+planKineticCost π)/2 := by
    obtain ⟨δ,hδ,H⟩ := hπ.uniform_plan_increment hfin hb hgeo hf.2.1 hε
    apply le_of_tendsto hlimit
    have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < δ :=
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0)).eventually_lt_const hδ
    filter_upwards [self_mem_nhdsWithin,hsmall] with h hh hhd
    change 0 < h at hh
    rw [div_le_iff₀ hh,hpair,hpair,← integral_sub (hJi (s+h)) (hJi s)]
    have H' := integral_mono_ae ((hJi (s+h)).sub (hJi s))
      ((((hHi s).add (integrable_const ε)).add (integrable_const (planKineticCost π))).const_mul (h/2))
      (ae_of_all _ fun r => by
        have hr := H (s-r) h hh hhd
        simpa only [show s-r+h = s+h-r by ring,Pi.sub_apply,Pi.add_apply] using hr)
    simp only [integral_const_mul, Pi.add_apply, Pi.sub_apply] at H'
    have hI1 : Integrable (fun r => planGradientEnergy m π (f : X → ℝ)
        (clampTime (s-r))+ε) ν := (hHi s).add (integrable_const ε)
    rw [integral_add hI1 (integrable_const (planKineticCost π)),
      integral_add (hHi s) (integrable_const ε)] at H'
    simp only [integral_const,probReal_univ,one_smul] at H'
    nlinarith [H']
  rw [real_inner_comm f v,henergy]
  apply le_of_forall_pos_le_add
  intro ε hε
  have H := hεbound ε hε
  linarith

lemma IsTestPlan.smoothDensity_action (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {B : ℝ≥0} (hB : ∀ t : Time, π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    {u : Time → Lp ℝ 2 m} (hu : StronglyMeasurable u)
    (hun : ∀ t, ∀ᵐ x ∂m, 0 ≤ u t x)
    (hlaw : ∀ t, densityMeasure m (u t) = π.map (fun γ => γ t))
    (hnorm : ∀ t, ‖u t‖^2 ≤ (B : ℝ))
    {κ : ℝ → ℝ} (hκ : HasCompactSupport κ) (hc : ContDiff ℝ 1 κ)
    (hn : ∀ r, 0 ≤ κ r) (hm : ∫ r, κ r = 1) (s : ℝ) :
    FormActionBound m (smoothDensity κ u s) (smoothDensity (deriv κ) u s) (planKineticCost π) := by
  let := kernelMeasure_probability (hc.continuous.integrable_of_hasCompactSupport hκ) hn hm
  have he : smoothDensity κ u = fun z => ∫ r, u (clampTime (z-r)) ∂kernelMeasure κ := by
    funext z
    exact smoothDensity_eq_average hc.continuous hn u z
  have hd := smoothDensity_hasDerivAt hκ hc hu hnorm s
  rw [he] at hd ⊢
  exact hπ.average_density_action hfin hb hgeo hB hu hun hlaw hnorm (kernelMeasure κ) hd

end WeakHessian

end
end

end OAI
