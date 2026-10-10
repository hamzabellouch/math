import OAI.Analysis.RCDHeat.SobolevTestPlan

namespace OAI

/-! # Flux and initial slope at every interior time of a geodesic plan -/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem testPlan_flux_fubini_interval (μ : Measure X)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    (G : Lp ℝ 2 μ) (s t : Time) (hst : (s:ℝ) ≤ t) :
    Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)*
      (∫ r in (s:ℝ)..(t:ℝ), G (geodesicExtension γ r))) π ∧
    (∫ γ : C(Time,X), dist (γ 0) (γ 1)*
      (∫ r in (s:ℝ)..(t:ℝ), G (geodesicExtension γ r)) ∂π) =
      ∫ r in (s:ℝ)..(t:ℝ), (∫ γ : C(Time,X),
        dist (γ 0) (γ 1)*G (geodesicExtension γ r) ∂π) := by
  have hi := (testPlan_length_memLp π hD).integrable_mul
    (testPlanMeasure_eval_memLp μ π hC hcomp G)
  have hit : Integrable (fun q : ℝ × C(Time,X) =>
      dist (q.2 0) (q.2 1)*G (geodesicExtension q.2 q.1))
      ((volume.restrict (Icc (s:ℝ) (t:ℝ))).prod π) := by
    apply hi.mono_measure
    exact Measure.prod_mono (Measure.restrict_mono (Icc_subset_Icc s.2.1 t.2.2) le_rfl) le_rfl
  have he (γ : C(Time,X)) :
      dist (γ 0) (γ 1)*(∫ r in (s:ℝ)..(t:ℝ), G (geodesicExtension γ r)) =
      ∫ r in Icc (s:ℝ) (t:ℝ), dist (γ 0) (γ 1)*G (geodesicExtension γ r) := by
    rw [integral_const_mul,integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hst]
  constructor
  · simpa only [he] using hit.integral_prod_right
  · simp_rw [he]
    rw [← integral_prod_symm _ hit,integral_prod _ hit,integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hst]

theorem IsRelaxedSlope.testPlan_integrated_interval (μ : Measure X)
    (π : Measure C(Time,X)) [IsFiniteMeasure π] (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G) (s t : Time) (hst : (s:ℝ) ≤ t) :
    (∫ γ : C(Time,X), |u (γ t)-u (γ s)| ∂π) ≤
      ∫ r in (s:ℝ)..(t:ℝ), (∫ γ : C(Time,X),
        dist (γ 0) (γ 1)*G (geodesicExtension γ r) ∂π) := by
  have hiu (r : Time) : MemLp (fun γ : C(Time,X) => u (γ r)) 2 π :=
    compressionPullback_memLp μ π _ (measurable_path_eval r) hC (hcomp r) u
  have hleft : Integrable (fun γ : C(Time,X) => |u (γ t)-u (γ s)|) π :=
    ((hiu t).sub (hiu s)).integrable (by norm_num) |>.abs
  obtain ⟨hri,he⟩ := testPlan_flux_fubini_interval μ π hC hcomp hD G s t hst
  rw [← he]
  exact integral_mono_ae hleft hri (hG.testPlan_ae_subinterval μ π hgeo hC hcomp hD s t hst)

theorem IsRelaxedSlope.testPlan_right_slope_bound (μ : Measure X)
    [ProperSpace X] [μ.Regular] (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G)
    (s : Time) (hs : (s:ℝ) < 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝[>] (s:ℝ),
      (∫ γ : C(Time,X), |u (geodesicExtension γ t)-u (γ s)| ∂π)/(t-s) <
        (∫ γ : C(Time,X), dist (γ 0) (γ 1)*G (γ s) ∂π)+ε := by
  let F : ℝ → ℝ := fun r => ∫ γ : C(Time,X),
    dist (γ 0) (γ 1)*G (geodesicExtension γ r) ∂π
  have hF : Continuous F := testPlan_flux_continuous μ π hgeo hC hcomp hD G
  have hd : HasDerivAt (fun t => ∫ r in (s:ℝ)..t, F r) (F s) s :=
    intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable _ _)
      hF.aestronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt
  have ht : Tendsto (fun t => (∫ r in (s:ℝ)..t, F r)/(t-s))
      (𝓝[≠] (s:ℝ)) (𝓝 (F s)) := by
    simpa only [slope_fun_def_field,intervalIntegral.integral_same,sub_zero] using hd.tendsto_slope
  have hfilt : 𝓝[>] (s:ℝ) ≤ 𝓝[≠] (s:ℝ) :=
    nhdsWithin_mono _ (fun t ht => (ne_of_gt ht : t ≠ (s:ℝ)))
  have hb := (ht.mono_left hfilt).eventually (gt_mem_nhds (lt_add_of_pos_right (F s) hε))
  have hsmall : ∀ᶠ t in 𝓝[>] (s:ℝ), t < 1 :=
    (gt_mem_nhds hs).filter_mono nhdsWithin_le_nhds
  filter_upwards [hb,hsmall,self_mem_nhdsWithin] with t ht ht1 hts
  have h01 : t ∈ Icc (0:ℝ) 1 := ⟨s.2.1.trans hts.le,ht1.le⟩
  have hi := hG.testPlan_integrated_interval μ π hgeo hC hcomp hD s ⟨t,h01⟩ hts.le
  have he (γ : C(Time,X)) : geodesicExtension γ t = γ ⟨t,h01⟩ :=
    geodesicExtension_eq γ ⟨t,h01⟩
  have hz : F s = ∫ γ : C(Time,X), dist (γ 0) (γ 1)*G (γ s) ∂π := by
    simp only [F,geodesicExtension_eq]
  rw [← hz]
  calc
    _ = (∫ γ : C(Time,X), |u (γ ⟨t,h01⟩)-u (γ s)| ∂π)/(t-s) := by simp_rw [he]
    _ ≤ (∫ r in (s:ℝ)..t, F r)/(t-s) := div_le_div_of_nonneg_right hi (sub_nonneg.mpr hts.le)
    _ < F s+ε := ht

end RegularPointCoordinates

end

end OAI
