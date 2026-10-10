import Mathlib
import OAI.Geometry.CubicTorus.Regularity.BVRadialVariation

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma finiteMeasure_coverBall (r : ℝ) :
    IsFiniteMeasure (volume.restrict (Metric.ball (0 : Cover) r)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact Metric.isBounded_ball.measure_lt_top⟩

lemma integral_halfspaceIndicator_unitBall {n : Cover} (hn : ‖n‖ = 1) :
    (∫ x in Metric.ball (0 : Cover) 1, halfspaceIndicator n x) =
      volume.real (Metric.ball (0 : Cover) 1) / 2 := by
  have := finiteMeasure_coverBall 1
  have hi : IntegrableOn (halfspaceIndicator n) (Metric.ball (0 : Cover) 1) :=
    Integrable.of_bound (measurable_halfspaceIndicator n).aestronglyMeasurable 1
      (Eventually.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using halfspaceIndicator_bound n x)
  have hi' : IntegrableOn (fun x : Cover ↦ halfspaceIndicator n (-x)) (Metric.ball 0 1) :=
    Integrable.of_bound ((measurable_halfspaceIndicator n).comp measurable_neg).aestronglyMeasurable 1
      (Eventually.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using halfspaceIndicator_bound n (-x))
  have he : (∫ x in Metric.ball (0 : Cover) 1, halfspaceIndicator n (-x)) =
      ∫ x in Metric.ball (0 : Cover) 1, halfspaceIndicator n x := by
    have h := integral_neg_eq_self ((Metric.ball (0 : Cover) 1).indicator (halfspaceIndicator n)) volume
    have hh : (fun x : Cover ↦ (Metric.ball (0 : Cover) 1).indicator (halfspaceIndicator n) (-x)) =
        (Metric.ball (0 : Cover) 1).indicator (fun x ↦ halfspaceIndicator n (-x)) := by
      ext x
      have hx : -x ∈ Metric.ball (0 : Cover) 1 ↔ x ∈ Metric.ball (0 : Cover) 1 := by simp
      by_cases hh : x ∈ Metric.ball (0 : Cover) 1 <;> simp [hx, hh]
    rw [hh, integral_indicator Metric.isOpen_ball.measurableSet,
      integral_indicator Metric.isOpen_ball.measurableSet] at h
    exact h
  have hsum : (∫ x in Metric.ball (0 : Cover) 1,
      halfspaceIndicator n x + halfspaceIndicator n (-x)) = volume.real (Metric.ball (0 : Cover) 1) := by
    have heq : (fun x : Cover ↦ halfspaceIndicator n x + halfspaceIndicator n (-x)) =ᵐ[
        volume.restrict (Metric.ball (0 : Cover) 1)] (fun _ ↦ (1 : ℝ)) := by
      have hne : ∀ᵐ x ∂(volume : Measure Cover), ⟪n, x⟫ ≠ 0 := by
        simpa only [ae_iff, not_not] using hyperplane_volume_zero hn
      filter_upwards [ae_restrict_of_ae hne] with x hx
      rcases lt_or_gt_of_ne hx with hneg | hpos
      · simp [halfspaceIndicator, inner_neg_right, hneg, not_lt_of_ge (neg_nonneg.mpr hneg.le)]
      · simp [halfspaceIndicator, inner_neg_right, not_lt_of_ge hpos.le, neg_neg_of_pos hpos]
    rw [integral_congr_ae heq, integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one]
  rw [integral_add hi hi', he] at hsum
  linarith

lemma integral_characteristic_chart {U : Set Torus} (hU : MeasurableSet U)
    (c : Torus) {r : ℝ} (hr : r ≤ 1 / 2) :
    (∫ x in Metric.ball (0 : Cover) r, characteristic U (quotientMap x + c)) =
      torusVolume.real (U ∩ Metric.ball c r) := by
  have h := integral_map (μ := volume.restrict (Metric.ball (0 : Cover) r))
    (measurable_quotientMap.add_const c).aemeasurable
    (measurable_characteristic hU).aestronglyMeasurable
  rw [torusVolume_chart_map_restrict c hr] at h
  rw [← h]
  simp only [characteristic, integral_indicator hU, Measure.restrict_restrict hU,
    integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one]

lemma integral_rescaled_characteristic {U : Set Torus} (hU : MeasurableSet U)
    (c : Torus) {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1 / 2) :
    (∫ x in Metric.ball (0 : Cover) 1, characteristic U (quotientMap (r • x) + c)) =
      torusVolume.real (U ∩ Metric.ball c r) / r ^ 3 := by
  let g : Cover → ℝ := (Metric.ball (0 : Cover) r).indicator (fun x ↦ characteristic U (quotientMap x + c))
  have he : (fun x : Cover ↦ g (r • x)) = (Metric.ball (0 : Cover) 1).indicator
      (fun x ↦ characteristic U (quotientMap (r • x) + c)) := by
    ext x
    have hx : r • x ∈ Metric.ball (0 : Cover) r ↔ x ∈ Metric.ball (0 : Cover) 1 := by
      simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hr.le]
      constructor <;> intro h <;> nlinarith
    by_cases hh : x ∈ Metric.ball (0 : Cover) 1 <;> simp [g, hx, hh]
  have h := Measure.integral_comp_smul (volume : Measure Cover) g r
  rw [he, integral_indicator Metric.isOpen_ball.measurableSet] at h
  have hg : (∫ x, g x) = torusVolume.real (U ∩ Metric.ball c r) := by
    rw [show g = (Metric.ball (0 : Cover) r).indicator (fun x ↦ characteristic U (quotientMap x + c)) from rfl,
      integral_indicator Metric.isOpen_ball.measurableSet, integral_characteristic_chart hU c hrsmall]
  rw [hg, show Module.finrank ℝ Cover = 3 by simp [Cover], smul_eq_mul,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr.le 3))] at h
  simpa only [div_eq_mul_inv, mul_comm] using h

lemma HalfspaceTrappedAt.tendsto_rescaled_volume {U : Set Torus} (hU : MeasurableSet U)
    {c : Torus} {n : Cover} (hn : ‖n‖ = 1) (htrap : HalfspaceTrappedAt U c n) :
    Tendsto (fun r : ℝ ↦ torusVolume.real (U ∩ Metric.ball c r) / r ^ 3)
      (𝓝[>] 0) (𝓝 (volume.real (Metric.ball (0 : Cover) 1) / 2)) := by
  have := finiteMeasure_coverBall 1
  have hlim := htrap.tendsto_integral_deviation hU hn
  have hi₁ (r : ℝ) : IntegrableOn
      (fun x : Cover ↦ characteristic U (quotientMap (r • x) + c)) (Metric.ball 0 1) := by
    have hc : Continuous (fun x : Cover ↦ quotientMap (r • x) + c) :=
      by
        have hs : Continuous (fun x : Cover ↦ r • x) := continuous_id.const_smul r
        exact (continuous_quotientMap.comp hs).add continuous_const
    exact Integrable.of_bound ((measurable_characteristic hU).comp hc.measurable).aestronglyMeasurable 1
      (Eventually.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using characteristic_bound U (quotientMap (r • x) + c))
  have hi₂ : IntegrableOn (halfspaceIndicator n) (Metric.ball (0 : Cover) 1) :=
    Integrable.of_bound (measurable_halfspaceIndicator n).aestronglyMeasurable 1
      (Eventually.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using halfspaceIndicator_bound n x)
  have hb (r : ℝ) : |(∫ x in Metric.ball (0 : Cover) 1, characteristic U (quotientMap (r • x) + c)) -
      volume.real (Metric.ball (0 : Cover) 1) / 2| ≤
      ∫ x in Metric.ball (0 : Cover) 1, |characteristic U (quotientMap (r • x) + c) - halfspaceIndicator n x| := by
    rw [← integral_halfspaceIndicator_unitBall hn, ← integral_sub (hi₁ r) hi₂]
    simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
      (μ := volume.restrict (Metric.ball (0 : Cover) 1))
      (fun x ↦ characteristic U (quotientMap (r • x) + c) - halfspaceIndicator n x))
  have hlim' : Tendsto (fun r : ℝ ↦ ∫ x in Metric.ball (0 : Cover) 1,
      characteristic U (quotientMap (r • x) + c)) (𝓝[>] 0)
      (𝓝 (volume.real (Metric.ball (0 : Cover) 1) / 2)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun r ↦ by simpa only [Real.norm_eq_abs] using hb r) hlim
  apply hlim'.congr'
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with r hr hrsmall
  exact integral_rescaled_characteristic hU c hr (le_of_lt hrsmall)

theorem isMinimizerAt_volume_density_half_ae {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∀ᵐ c ∂(spatialNormalMeasure μ : Measure Torus),
      Tendsto (fun r : ℝ ↦ torusVolume.real (openRepresentative E ∩ Metric.ball c r) / r ^ 3)
        (𝓝[>] 0) (𝓝 (volume.real (Metric.ball (0 : Cover) 1) / 2)) := by
  obtain ⟨N, hN, hpolar, hn⟩ := normalMeasure_polar_unit hμ
  filter_upwards [isMinimizerAt_halfspace_trapped_ae hV hE hmin hμ hN hpolar hn, hn]
    with c hc hnc
  exact hc.tendsto_rescaled_volume (isOpen_openRepresentative E).measurableSet hnc

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma divergence_of_notMem_tsupport {F : Cover → Cover} {x : Cover}
    (hx : x ∉ tsupport F) : divergence F x = 0 := by
  simp [divergence, fderiv_of_notMem_tsupport ℝ hx]

lemma divergence_tsupport_subset (F : Cover → Cover) :
    tsupport (divergence F) ⊆ tsupport F := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hh
  exact hx (divergence_of_notMem_tsupport hh)

theorem normalMeasure_local_flux {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    (∫ z, ⟪(z.2 : Cover), F z.1⟫ ∂(μ : Measure NormalBundle)) =
      ∫ x : Cover, characteristic E (quotientMap x) * divergence F x := by
  let G := latticePeriodize F
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := latticePeriodize_contDiff hF hc
  have hGp : ∀ n x, G (x + latticeVector n) = G x := latticePeriodize_periodic F
  obtain ⟨M, hM, hb⟩ := periodic_bounded hG.continuous hGp
  have hflux := normalMeasure_flux hμ hG hGp (by linarith : 0 < M + 1)
    (fun x ↦ (hb x).trans (by linarith : M ≤ M + 1))
  have he (z : NormalBundle) : G z.1 = F z.1 :=
    (latticePeriodize_eventuallyEq hc hs (compactCell_coordinates z.1)).eq_of_nhds
  change (∫ z, ⟪(z.2 : Cover), G z.1⟫ ∂(μ : Measure NormalBundle)) = _ at hflux
  simp_rw [he] at hflux
  have hdiv : (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence G x) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_fundamentalCube.inter (hE.preimage measurable_quotientMap))]
      with x hx
    have hd := (latticePeriodize_eventuallyEq hc hs (fun i ↦ ⟨(hx.1 i).1, (hx.1 i).2.le⟩)).fderiv_eq (𝕜 := ℝ)
    simp only [divergence, G, hd]
  rw [hdiv] at hflux
  rw [hflux, ← integral_indicator (measurableSet_fundamentalCube.inter (hE.preimage measurable_quotientMap))]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ fundamentalCube
  · by_cases he : quotientMap x ∈ E <;> simp [characteristic, hx, he]
  · have hd : divergence F x = 0 := by
      apply divergence_of_notMem_tsupport
      intro hh
      apply hx
      exact fun i ↦ ⟨(hs hh i).1.le, (hs hh i).2⟩
    simp [hx, hd]

lemma IsNormalMeasure.congr_ae {E F : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) (hEF : E =ᵐ[torusVolume] F) : IsNormalMeasure F μ := by
  refine ⟨?_, ?_⟩
  · rw [← perimeter_congr_ae hEF]
    exact hμ.1
  · intro G hG
    rw [hμ.2 G hG]
    apply setIntegral_congr_set
    exact liftSet_congr_ae hEF

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

def scaledTestField (a : Cover) (r : ℝ) (F : Cover → Cover) (x : Cover) : Cover :=
  r • F (r⁻¹ • (x - a))

lemma scaledTestField_contDiff {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (a : Cover) (r : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (scaledTestField a r F) :=
  (hF.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)).const_smul r

lemma fderiv_scaledTestField {F : Cover → Cover} (hF : Differentiable ℝ F)
    (a x : Cover) {r : ℝ} (hr : r ≠ 0) :
    fderiv ℝ (scaledTestField a r F) x = fderiv ℝ F (r⁻¹ • (x - a)) := by
  have hψ : HasFDerivAt (fun y : Cover ↦ r⁻¹ • (y - a))
      (r⁻¹ • (ContinuousLinearMap.id ℝ Cover)) x :=
    ((hasFDerivAt_id x).sub_const a).const_smul r⁻¹
  have h := (((hF _).hasFDerivAt).comp x hψ).const_smul r
  change HasFDerivAt (scaledTestField a r F) _ x at h
  rw [h.fderiv]
  ext v
  simp [smul_smul, hr]

lemma divergence_scaledTestField {F : Cover → Cover} (hF : Differentiable ℝ F)
    (a x : Cover) {r : ℝ} (hr : r ≠ 0) :
    divergence (scaledTestField a r F) x = divergence F (r⁻¹ • (x - a)) := by
  simp only [divergence, fderiv_scaledTestField hF a x hr]

lemma scaledTestField_tsupport {F : Cover → Cover}
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1)
    (a : Cover) {r : ℝ} (hr : 0 < r) :
    tsupport (scaledTestField a r F) ⊆ Metric.closedBall a r := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have hFx : F (r⁻¹ • (x - a)) ≠ 0 := by
    intro h
    exact hx (by simp [scaledTestField, h])
  have hb := hs (subset_closure hFx)
  have hb' : ‖x - a‖ / r ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hr.le), div_eq_inv_mul] using hb
  exact (div_le_iff₀ hr).mp hb' |>.trans_eq (one_mul r)

lemma scaledTestField_hasCompactSupport {F : Cover → Cover}
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1)
    (a : Cover) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (scaledTestField a r F) :=
  (isCompact_closedBall a r).of_isClosed_subset isClosed_closure (scaledTestField_tsupport hs a hr)

lemma integral_cover_affine_scaling (g : Cover → ℝ) (a : Cover) {r : ℝ} (hr : 0 < r) :
    (∫ x, g x) = r ^ 3 * ∫ y : Cover, g (r • y + a) := by
  have h := Measure.integral_comp_smul (volume : Measure Cover) (fun x ↦ g (x + a)) r
  rw [integral_add_right_eq_self, show Module.finrank ℝ Cover = 3 by simp [Cover],
    smul_eq_mul, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr.le 3))] at h
  rw [h]
  field_simp

theorem normalMeasure_scaled_flux {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1)
    (a : Cover) {r : ℝ} (hr : 0 < r)
    (hc : Metric.closedBall a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    (∫ z, ⟪(z.2 : Cover), F (r⁻¹ • ((z.1 : Cover) - a))⟫ ∂(μ : Measure NormalBundle)) / r ^ 2 =
      ∫ x : Cover, characteristic E (quotientMap (r • x + a)) * divergence F x := by
  have hflux := normalMeasure_local_flux hE hμ (scaledTestField_contDiff hF a r)
    (scaledTestField_hasCompactSupport hs a hr) ((scaledTestField_tsupport hs a hr).trans hc)
  simp only [scaledTestField, inner_smul_right, integral_const_mul] at hflux
  have hscale := integral_cover_affine_scaling
    (fun x ↦ characteristic E (quotientMap x) * divergence (scaledTestField a r F) x) a hr
  have hdiv (x : Cover) : divergence (scaledTestField a r F) (r • x + a) = divergence F x := by
    rw [divergence_scaledTestField (hF.differentiable (by simp)) a _ hr.ne']
    simp [hr.ne']
  simp_rw [hdiv] at hscale
  rw [hscale] at hflux
  calc
    _ = (r * ∫ z, ⟪(z.2 : Cover), F (r⁻¹ • ((z.1 : Cover) - a))⟫ ∂(μ : Measure NormalBundle)) / r ^ 3 := by
      field_simp
    _ = _ := by rw [hflux]; field_simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem HalfspaceTrappedAt.tendsto_test_integral {U : Set Torus} (hU : MeasurableSet U)
    {c : Torus} {n : Cover} (hn : ‖n‖ = 1) (htrap : HalfspaceTrappedAt U c n)
    {g : Cover → ℝ} (hg : Continuous g) (hs : Function.support g ⊆ Metric.ball (0 : Cover) 1) :
    Tendsto (fun r : ℝ ↦ ∫ x : Cover, characteristic U (quotientMap (r • x) + c) * g x)
      (𝓝[>] 0) (𝓝 (∫ x : Cover, halfspaceIndicator n x * g x)) := by
  have := finiteMeasure_coverBall 1
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Cover) 1).exists_bound_of_continuousOn hg.continuousOn
  let K := |C| + 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hgK (x : Cover) (hx : x ∈ Metric.ball (0 : Cover) 1) : ‖g x‖ ≤ K :=
    (hC x (Metric.ball_subset_closedBall hx)).trans ((le_abs_self C).trans (by dsimp [K]; linarith))
  have hmeas (r : ℝ) : AEStronglyMeasurable
      (fun x : Cover ↦ characteristic U (quotientMap (r • x) + c) * g x)
      (volume.restrict (Metric.ball (0 : Cover) 1)) := by
    have hmap : Continuous (fun x : Cover ↦ quotientMap (r • x) + c) :=
      (continuous_quotientMap.comp (continuous_id.const_smul r)).add continuous_const
    exact (((measurable_characteristic hU).comp hmap.measurable).mul hg.measurable).aestronglyMeasurable
  have hb (r : ℝ) : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : Cover) 1)),
      ‖characteristic U (quotientMap (r • x) + c) * g x‖ ≤ K := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    rw [norm_mul]
    have hh : ‖characteristic U (quotientMap (r • x) + c)‖ ≤ 1 := by
      simpa only [Real.norm_eq_abs] using characteristic_bound U (quotientMap (r • x) + c)
    exact (mul_le_mul hh (hgK x hx) (norm_nonneg _) (by norm_num)).trans_eq (one_mul K)
  have hlim : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : Cover) 1)),
      Tendsto (fun r : ℝ ↦ characteristic U (quotientMap (r • x) + c) * g x)
        (𝓝[>] 0) (𝓝 (halfspaceIndicator n x * g x)) := by
    have hne : ∀ᵐ x ∂(volume : Measure Cover), ⟪n, x⟫ ≠ 0 := by
      simpa only [ae_iff, not_not] using hyperplane_volume_zero hn
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet, ae_restrict_of_ae hne]
      with x hx hnx
    apply tendsto_const_nhds.congr'
    filter_upwards [htrap.eventually_characteristic (by simpa using hx) hnx] with r hr
    rw [hr]
  have ht := tendsto_integral_filter_of_dominated_convergence (fun _ : Cover ↦ K)
    (Eventually.of_forall hmeas) (Eventually.of_forall hb) (integrable_const _) hlim
  have hzero (x : Cover) (hx : x ∉ Metric.ball (0 : Cover) 1) : g x = 0 := by
    by_contra hh
    exact hx (hs hh)
  have he (r : ℝ) := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := (volume : Measure Cover)) (s := Metric.ball (0 : Cover) 1)
    (f := fun x ↦ characteristic U (quotientMap (r • x) + c) * g x)
    (fun x hx ↦ by rw [hzero x hx, mul_zero])
  have he' := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := (volume : Measure Cover)) (s := Metric.ball (0 : Cover) 1)
    (f := fun x ↦ halfspaceIndicator n x * g x)
    (fun x hx ↦ by rw [hzero x hx, mul_zero])
  simpa only [he, he'] using ht

theorem normalMeasure_scaled_flux_limit {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {a n : Cover} (hn : ‖n‖ = 1) (htrap : HalfspaceTrappedAt E (quotientMap a) n)
    {R : ℝ} (hR : 0 < R)
    (hc : Metric.closedBall a R ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.ball (0 : Cover) 1) :
    Tendsto (fun r : ℝ ↦
      (∫ z, ⟪(z.2 : Cover), F (r⁻¹ • ((z.1 : Cover) - a))⟫ ∂(μ : Measure NormalBundle)) / r ^ 2)
      (𝓝[>] 0) (𝓝 (∫ x : Cover, halfspaceIndicator n x * divergence F x)) := by
  have ht := htrap.tendsto_test_integral hE hn (continuous_divergence hF)
    (((subset_tsupport _).trans (divergence_tsupport_subset F)).trans hs)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hR)]
    with r hr hrR
  have he := normalMeasure_scaled_flux hE hμ hF (hs.trans Metric.ball_subset_closedBall) a hr
    ((Metric.closedBall_subset_closedBall (le_of_lt hrR)).trans hc)
  simp only [quotientMap_add] at he
  exact he.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma scalar_test_normal_error {μ : FiniteMeasure NormalBundle}
    {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hunit : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {n : Cover} (hn : ‖n‖ = 1) {ψ : Cover → ℝ} (hψ : Continuous ψ)
    (hs : Function.support ψ ⊆ Metric.closedBall (0 : Cover) 1)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, |ψ x| ≤ C) (a : Cover) {r : ℝ} (hr : 0 < r) :
    |(∫ z, ψ (r⁻¹ • ((z.1 : Cover) - a)) ∂(μ : Measure NormalBundle)) / r ^ 2 -
      (∫ z, ⟪(z.2 : Cover), ψ (r⁻¹ • ((z.1 : Cover) - a)) • n⟫ ∂(μ : Measure NormalBundle)) / r ^ 2| ≤
      C * normalOscillation (spatialNormalMeasure μ) N (quotientMap a) n r := by
  let f : NormalBundle → ℝ := fun z ↦ ψ (r⁻¹ • ((z.1 : Cover) - a))
  have hf : Continuous f := hψ.comp ((continuous_subtype_val.comp continuous_fst).sub continuous_const |>.const_smul r⁻¹)
  have hfi := hf.integrable_of_hasCompactSupport (μ := (μ : Measure NormalBundle))
    (HasCompactSupport.of_compactSpace _)
  have hν : Continuous (fun z : NormalBundle ↦ ⟪(z.2 : Cover), n⟫) :=
    (continuous_subtype_val.comp continuous_snd).inner continuous_const
  have hgi : Integrable (fun z ↦ f z * ⟪(z.2 : Cover), n⟫) (μ : Measure NormalBundle) := (hf.mul hν).integrable_of_hasCompactSupport (μ := (μ : Measure NormalBundle))
    (HasCompactSupport.of_compactSpace _)
  let B := Metric.closedBall (quotientMap a) r
  let g : Torus → ℝ := B.indicator (fun x ↦ C * ‖N x - n‖)
  have hg : Measurable g := ((hN.sub_const n).norm.const_mul C).indicator Metric.isClosed_closedBall.measurableSet
  have hgi' : Integrable g (spatialNormalMeasure μ : Measure Torus) :=
    ((integrable_norm_sub_normal hN hunit n).const_mul C).indicator Metric.isClosed_closedBall.measurableSet
  have hgm : Integrable (fun z : NormalBundle ↦ g (normalProjection z)) (μ : Measure NormalBundle) :=
    (integrable_map_measure hg.aestronglyMeasurable normalProjection_continuous.measurable.aemeasurable).mp hgi'
  have hz (z : NormalBundle) (hz : normalProjection z ∉ B) : f z = 0 := by
    by_contra hh
    have hb' := hs hh
    have hv : ‖(z.1 : Cover) - a‖ ≤ r := by
      have hh' : ‖(z.1 : Cover) - a‖ / r ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.mpr hr.le), div_eq_inv_mul] using hb'
      simpa using (div_le_iff₀ hr).mp hh'
    apply hz
    change dist (quotientMap z.1) (quotientMap a) ≤ r
    rw [dist_eq_norm, ← quotientMap_sub]
    exact (norm_quotientMap_le _).trans hv
  have he : ∀ᵐ z ∂(μ : Measure NormalBundle),
      ‖f z - f z * ⟪(z.2 : Cover), n⟫‖ ≤ g (normalProjection z) := by
    filter_upwards [hpolar] with z hp
    by_cases hzB : normalProjection z ∈ B
    · simp only [g, indicator_of_mem hzB, Real.norm_eq_abs]
      change |f z - f z * ⟪(z.2 : Cover), n⟫| ≤ C * ‖N (quotientMap z.1) - n‖
      rw [hp, show f z - f z * ⟪(z.2 : Cover), n⟫ = f z * (1 - ⟪(z.2 : Cover), n⟫) by ring, abs_mul]
      have hi : |1 - ⟪(z.2 : Cover), n⟫| ≤ ‖(z.2 : Cover) - n‖ := by
        have hnn : ⟪n, n⟫ = 1 := by simp [hn]
        have hh := abs_real_inner_le_norm ((z.2 : Cover) - n) n
        rw [hn, mul_one, inner_sub_left, hnn, abs_sub_comm] at hh
        exact hh
      exact mul_le_mul (hb _) hi (abs_nonneg _) hC
    · simp [g, hzB, hz z hzB]
  have hi := norm_integral_le_of_norm_le hgm he
  rw [integral_sub hfi hgi, ← integral_spatialNormalMeasure μ hg] at hi
  simp only [g, B, integral_indicator Metric.isClosed_closedBall.measurableSet, integral_const_mul,
    Real.norm_eq_abs] at hi
  simp only [inner_smul_right]
  rw [← sub_div, abs_div, abs_of_nonneg (sq_nonneg r)]
  exact (div_le_div_of_nonneg_right hi (sq_nonneg r)).trans_eq (by
    dsimp [normalOscillation, B, f]; ring)

theorem normalMeasure_scalar_tangent {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hunit : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {a n : Cover} (hn : ‖n‖ = 1) (htrap : HalfspaceTrappedAt E (quotientMap a) n)
    (hosc : Tendsto (normalOscillation (spatialNormalMeasure μ) N (quotientMap a) n) (𝓝[>] 0) (𝓝 0))
    {R : ℝ} (hR : 0 < R)
    (hc : Metric.closedBall a R ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : tsupport ψ ⊆ Metric.ball (0 : Cover) 1) :
    Tendsto (fun r : ℝ ↦ (∫ z, ψ (r⁻¹ • ((z.1 : Cover) - a)) ∂(μ : Measure NormalBundle)) / r ^ 2)
      (𝓝[>] 0) (𝓝 (∫ x : Cover, halfspaceIndicator n x * divergence (fun y ↦ ψ y • n) x)) := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ ψ x • n) := hψ.smul_const n
  have hFs : tsupport (fun x ↦ ψ x • n) ⊆ Metric.ball (0 : Cover) 1 := by
    apply subset_trans _ hs
    exact tsupport_smul_subset_left (f := ψ) (g := fun _ ↦ n)
  have hflux := normalMeasure_scaled_flux_limit hE hμ hn htrap hR hc hF hFs
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Cover) 1).exists_bound_of_continuousOn hψ.continuous.continuousOn
  let K := |C| + 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hb (x : Cover) : |ψ x| ≤ K := by
    by_cases hx : x ∈ Metric.closedBall (0 : Cover) 1
    · have hh : |ψ x| ≤ C := by simpa only [Real.norm_eq_abs] using hC x hx
      exact hh.trans ((le_abs_self C).trans (by dsimp [K]; linarith))
    · have hz : ψ x = 0 := by
        by_contra hh
        exact hx (Metric.ball_subset_closedBall (hs (subset_tsupport _ hh)))
      simp only [hz, abs_zero]; exact hK
  have hd : Tendsto (fun r : ℝ ↦
      (∫ z, ψ (r⁻¹ • ((z.1 : Cover) - a)) ∂(μ : Measure NormalBundle)) / r ^ 2 -
      (∫ z, ⟪(z.2 : Cover), ψ (r⁻¹ • ((z.1 : Cover) - a)) • n⟫ ∂(μ : Measure NormalBundle)) / r ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa only [mul_zero] using hosc.const_mul K)
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa only [Real.norm_eq_abs] using scalar_test_normal_error hN hpolar hunit hn hψ.continuous
      ((subset_tsupport _).trans (hs.trans Metric.ball_subset_closedBall)) hK hb a hr
  have ht := hflux.add hd
  simpa only [add_sub_cancel, add_zero] using ht

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalRotation (n : Cover) : Cover ≃ₗᵢ[ℝ] Cover :=
  Submodule.reflection (ℝ ∙ (EuclideanSpace.single 0 1 - n))ᗮ

lemma normalRotation_axis {n : Cover} (hn : ‖n‖ = 1) :
    normalRotation n (EuclideanSpace.single 0 1) = n := by
  apply Submodule.reflection_sub
  simpa using hn.symm

def normalProductChart (n : Cover) : (ℝ × (Fin 2 → ℝ)) ≃ᵐ Cover :=
  ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).symm.trans
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))).trans (normalRotation n).toMeasurableEquiv

lemma normalProductChart_apply (n : Cover) (t : ℝ) (y : Fin 2 → ℝ) :
    normalProductChart n (t, y) = normalRotation n (WithLp.toLp 2 (Fin.cons t y)) := by
  simp [normalProductChart, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero']

lemma normalProductChart_measurePreserving (n : Cover) :
    MeasurePreserving (normalProductChart n) := by
  exact (((volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).symm _).trans
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).symm).trans
    (normalRotation n).measurePreserving

lemma normalProductChart_decompose {n : Cover} (hn : ‖n‖ = 1) (t : ℝ) (y : Fin 2 → ℝ) :
    normalProductChart n (t, y) = t • n + normalProductChart n (0, y) := by
  rw [normalProductChart_apply, normalProductChart_apply]
  have he : (WithLp.toLp 2 (Fin.cons t y) : Cover) =
      t • EuclideanSpace.single 0 1 + WithLp.toLp 2 (Fin.cons 0 y) := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  rw [he, map_add, map_smul, normalRotation_axis hn]

lemma normalProductChart_inner {n : Cover} (hn : ‖n‖ = 1) (t : ℝ) (y : Fin 2 → ℝ) :
    ⟪n, normalProductChart n (t, y)⟫ = t := by
  rw [normalProductChart_apply]
  conv_lhs => lhs; rw [← normalRotation_axis hn]
  rw [(normalRotation n).inner_map_map]
  simp [EuclideanSpace.inner_single_left]

lemma normalProductChart_coord_bound {n : Cover} (hn : ‖n‖ = 1) (t : ℝ) (y : Fin 2 → ℝ) :
    |t| ≤ ‖normalProductChart n (t, y)‖ := by
  simpa only [normalProductChart_inner hn, hn, one_mul] using
    abs_real_inner_le_norm n (normalProductChart n (t, y))

lemma normalProductChart_line_contDiff {n : Cover} (hn : ‖n‖ = 1) (y : Fin 2 → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ normalProductChart n (t, y)) := by
  have he : (fun t ↦ normalProductChart n (t, y)) =
      (fun t ↦ t • n + normalProductChart n (0, y)) :=
    funext fun t ↦ normalProductChart_decompose hn t y
  rw [he]
  exact (contDiff_id.smul_const n).add contDiff_const

lemma normalProductChart_line_deriv {n : Cover} (hn : ‖n‖ = 1) (t : ℝ) (y : Fin 2 → ℝ) :
    HasDerivAt (fun s ↦ normalProductChart n (s, y)) n t := by
  have he : (fun t ↦ normalProductChart n (t, y)) =
      (fun t ↦ t • n + normalProductChart n (0, y)) :=
    funext fun t ↦ normalProductChart_decompose hn t y
  rw [he]
  simpa only [one_smul, add_zero, id_eq] using
    ((hasDerivAt_id t).smul_const n).add_const (normalProductChart n (0, y))

lemma halfspace_flux_integrable {n : Cover} {ψ : Cover → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    Integrable (fun x : Cover ↦ halfspaceIndicator n x * divergence (fun y ↦ ψ y • n) x) := by
  have hF := hψ.smul_const n
  have hc : HasCompactSupport (divergence (fun y ↦ ψ y • n)) :=
    (hs.of_isClosed_subset isClosed_closure
      (tsupport_smul_subset_left (f := ψ) (g := fun _ ↦ n))).of_isClosed_subset
        isClosed_closure (divergence_tsupport_subset _)
  exact (continuous_divergence hF).integrable_of_hasCompactSupport hc |>.bdd_mul
    (measurable_halfspaceIndicator n).aestronglyMeasurable
    (Eventually.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using halfspaceIndicator_bound n x)

theorem integral_halfspace_flux {n : Cover} (hn : ‖n‖ = 1) {ψ : Cover → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : tsupport ψ ⊆ Metric.closedBall (0 : Cover) 1) :
    (∫ x : Cover, halfspaceIndicator n x * divergence (fun y ↦ ψ y • n) x) =
      ∫ y : Fin 2 → ℝ, ψ (normalProductChart n (0, y)) := by
  have hcompact : HasCompactSupport ψ :=
    (isCompact_closedBall (0 : Cover) 1).of_isClosed_subset isClosed_closure hs
  let g : Cover → ℝ := fun x ↦ halfspaceIndicator n x * divergence (fun y ↦ ψ y • n) x
  have hi : Integrable g := halfspace_flux_integrable hψ hcompact
  have him : Integrable (fun z ↦ g (normalProductChart n z)) :=
    (normalProductChart_measurePreserving n).integrable_comp
      hi.aestronglyMeasurable |>.mpr hi
  have he (y : Fin 2 → ℝ) : (∫ t : ℝ, g (normalProductChart n (t, y))) =
      ψ (normalProductChart n (0, y)) := by
    let f : ℝ → ℝ := fun t ↦ ψ (normalProductChart n (t, y))
    have hf : ContDiff ℝ (⊤ : ℕ∞) f := hψ.comp (normalProductChart_line_contDiff hn y)
    have hfs : HasCompactSupport f := by
      apply (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).of_isClosed_subset isClosed_closure
      apply closure_minimal _ isClosed_Icc
      intro t ht
      have hb := hs (subset_tsupport _ ht)
      have hb' : ‖normalProductChart n (t, y)‖ ≤ 1 := by simpa using hb
      have habs := (normalProductChart_coord_bound hn t y).trans hb'
      exact abs_le.mp habs
    have hderiv (t : ℝ) : deriv f t = divergence (fun x ↦ ψ x • n) (normalProductChart n (t, y)) := by
      rw [divergence_smul_const (hψ.differentiable (by simp)).differentiableAt]
      exact (((hψ.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t
        (normalProductChart_line_deriv hn t y)).deriv
    have hg (t : ℝ) : g (normalProductChart n (t, y)) =
        (Iio (0 : ℝ)).indicator (deriv f) t := by
      by_cases ht : t < 0 <;>
        simp [g, halfspaceIndicator, normalProductChart_inner hn, ht, hderiv]
    simp_rw [hg]
    rw [integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio]
    exact hfs.integral_Iic_deriv_eq (hf.of_le (by simp)) 0
  rw [← (normalProductChart_measurePreserving n).integral_comp' g,
    Measure.volume_eq_prod]
  rw [integral_prod_symm (f := fun z : ℝ × (Fin 2 → ℝ) ↦ g (normalProductChart n z))
    (by simpa only [Measure.volume_eq_prod] using him)]
  exact integral_congr_ae (Eventually.of_forall he)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

def tangentPart (ν n : Cover) : Cover := n - ⟪ν, n⟫ • ν

lemma norm_tangentPart_sq {ν : Cover} (hν : ‖ν‖ = 1) (n : Cover) :
    ‖tangentPart ν n‖ ^ 2 = ‖n‖ ^ 2 - ⟪ν, n⟫ ^ 2 := by
  rw [tangentPart, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, inner_smul_right,
    real_inner_comm n ν, hν, mul_one, sq_abs]
  ring

lemma inner_tangentPart {ν : Cover} (hν : ‖ν‖ = 1) (n : Cover) :
    ⟪n, tangentPart ν n⟫ = ‖tangentPart ν n‖ ^ 2 := by
  rw [norm_tangentPart_sq hν, tangentPart, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm n ν]
  ring

lemma tangentialDivergence_smul_const {f : Cover → ℝ} {x : Cover}
    (hf : DifferentiableAt ℝ f x) (ν n : Cover) :
    tangentialDivergence (fun y ↦ f y • n) x ν = fderiv ℝ f x (tangentPart ν n) := by
  rw [tangentialDivergence, divergence_smul_const hf, fderiv_smul_const hf]
  simp only [ContinuousLinearMap.smulRight_apply, inner_smul_right, tangentPart,
    map_sub, map_smul, smul_eq_mul]
  ring

def heightTestField (ζ : Cover → ℝ) (a n x : Cover) : Cover :=
  (ζ x ^ 2 * ⟪n, x - a⟫) • n

lemma heightTestField_contDiff {ζ : Cover → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (a n : Cover) : ContDiff ℝ (⊤ : ℕ∞) (heightTestField ζ a n) :=
  ((hζ.pow 2).mul (contDiff_const.inner ℝ (contDiff_id.sub contDiff_const))).smul contDiff_const

lemma heightTestField_tsupport (ζ : Cover → ℝ) (a n : Cover) :
    tsupport (heightTestField ζ a n) ⊆ tsupport ζ := by
  apply closure_mono
  intro x hx
  by_contra hz
  exact hx (by simp [heightTestField, Function.notMem_support.mp hz])

lemma heightTestField_hasCompactSupport {ζ : Cover → ℝ} (hζ : HasCompactSupport ζ)
    (a n : Cover) : HasCompactSupport (heightTestField ζ a n) :=
  hζ.of_isClosed_subset isClosed_closure (heightTestField_tsupport ζ a n)

lemma tangentialDivergence_heightTestField {ζ : Cover → ℝ} {x : Cover}
    (hζ : DifferentiableAt ℝ ζ x) (a n : Cover) {ν : Cover} (hν : ‖ν‖ = 1) :
    tangentialDivergence (heightTestField ζ a n) x ν =
      ζ x ^ 2 * ‖tangentPart ν n‖ ^ 2 +
        2 * ζ x * ⟪n, x - a⟫ * fderiv ℝ ζ x (tangentPart ν n) := by
  have hh : HasFDerivAt (fun y : Cover ↦ ⟪n, y - a⟫) (innerSL ℝ n) x := by
    convert! ((innerSL ℝ n).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)) using 1
  have hφ := (hζ.hasFDerivAt.pow 2).mul hh
  change HasFDerivAt (fun y : Cover ↦ ζ y ^ 2 * ⟪n, y - a⟫) _ x at hφ
  change tangentialDivergence (fun y ↦ (ζ y ^ 2 * ⟪n, y - a⟫) • n) x ν = _
  rw [tangentialDivergence_smul_const hφ.differentiableAt, hφ.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, Nat.reduceSub,
    pow_one, innerSL_apply_apply, inner_tangentPart hν]
  ring

lemma heightTestField_tilt_bound {ζ : Cover → ℝ} {x : Cover}
    (hζ : DifferentiableAt ℝ ζ x) (a n : Cover) {ν : Cover} (hν : ‖ν‖ = 1) :
    ζ x ^ 2 * ‖tangentPart ν n‖ ^ 2 ≤
      2 * tangentialDivergence (heightTestField ζ a n) x ν +
        4 * ⟪n, x - a⟫ ^ 2 * ‖fderiv ℝ ζ x‖ ^ 2 := by
  rw [tangentialDivergence_heightTestField hζ a n hν]
  have hb : |fderiv ℝ ζ x (tangentPart ν n)| ≤
      ‖fderiv ℝ ζ x‖ * ‖tangentPart ν n‖ := by
    simpa only [Real.norm_eq_abs] using (fderiv ℝ ζ x).le_opNorm (tangentPart ν n)
  have hlo := neg_abs_le (ζ x * ⟪n, x - a⟫ * fderiv ℝ ζ x (tangentPart ν n))
  rw [abs_mul, abs_mul] at hlo
  have hb' := mul_le_mul_of_nonneg_left hb (mul_nonneg (abs_nonneg (ζ x)) (abs_nonneg ⟪n, x - a⟫))
  have hy := sq_nonneg (|ζ x| * ‖tangentPart ν n‖ - 2 * |⟪n, x - a⟫| * ‖fderiv ℝ ζ x‖)
  nlinarith [sq_abs (ζ x), sq_abs ⟪n, x - a⟫]

lemma heightTestField_flux_bound {ζ : Cover → ℝ} (a x : Cover)
    {ν n : Cover} (hν : ‖ν‖ = 1) (hn : ‖n‖ = 1) (H : ℝ) :
    H * ⟪ν, heightTestField ζ a n x⟫ ≤ |H| * (ζ x ^ 2 * |⟪n, x - a⟫|) := by
  have hi : |⟪ν, n⟫| ≤ 1 := by simpa only [hν, hn, mul_one] using abs_real_inner_le_norm ν n
  calc
    H * ⟪ν, heightTestField ζ a n x⟫ ≤ |H * ⟪ν, heightTestField ζ a n x⟫| := le_abs_self _
    _ = |H| * (ζ x ^ 2 * |⟪n, x - a⟫|) * |⟪ν, n⟫| := by
      simp only [heightTestField, inner_smul_right, abs_mul, abs_pow, sq_abs]
      ring
    _ ≤ |H| * (ζ x ^ 2 * |⟪n, x - a⟫|) := by
      exact mul_le_of_le_one_right (by positivity) hi

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma radialDensityWeight_le_one (a : Cover) (r ε : ℝ) (x : Cover) :
    radialDensityWeight a r ε x ≤ 1 := Real.smoothTransition.le_one _

lemma radialDensityWeight_tsupport {a : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    tsupport (radialDensityWeight a r ε) ⊆ Metric.closedBall a r := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hh
  exact hx (radialDensityWeight_zero hr hε (le_of_lt (by
    simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hh)))

lemma radialDensityWeight_hasCompactSupport {a : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    HasCompactSupport (radialDensityWeight a r ε) :=
  (isCompact_closedBall a r).of_isClosed_subset isClosed_closure (radialDensityWeight_tsupport hr hε)

lemma norm_fderiv_radialDensityWeight_le (a x : Cover) (r ε : ℝ) :
    ‖fderiv ℝ (radialDensityWeight a r ε) x‖ ≤ 2 * |radialDensitySlope a r ε x| * ‖x - a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [fderiv_radialDensityWeight, Real.norm_eq_abs, abs_mul, abs_mul]
  norm_num only [abs_neg, abs_of_pos (by norm_num : 0 < (2 : ℝ))]
  exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm (x - a) v) (by positivity) |>.trans_eq (by ring)

lemma norm_fderiv_radialDensityWeight_bound {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ K)
    (a x : Cover) {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    ‖fderiv ℝ (radialDensityWeight a r ε) x‖ ≤ 2 * K * r / ε := by
  have hs : |radialDensitySlope a r ε x| ≤ K / ε := by
    simp only [radialDensitySlope, abs_div, abs_of_pos hε]
    exact div_le_div_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hb ((r ^ 2 - ‖x - a‖ ^ 2) / ε)) hε.le
  by_cases hx : r ≤ ‖x - a‖
  · have hz : ‖fderiv ℝ (radialDensityWeight a r ε) x‖ = 0 := by
      apply le_antisymm _ (norm_nonneg _)
      simpa only [radialDensitySlope_zero hr hε hx, abs_zero, mul_zero, zero_mul] using
        norm_fderiv_radialDensityWeight_le a x r ε
    rw [hz]
    positivity
  · calc
      _ ≤ 2 * |radialDensitySlope a r ε x| * ‖x - a‖ := norm_fderiv_radialDensityWeight_le a x r ε
      _ ≤ 2 * (K / ε) * r := mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num))
        (le_of_not_ge hx) (norm_nonneg _) (by positivity)
      _ = _ := by ring

def radialHeightCutoff (a : Cover) (r : ℝ) : Cover → ℝ :=
  radialDensityWeight a (2 * r) (3 * r ^ 2)

lemma radialHeightCutoff_one {a x : Cover} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ Metric.closedBall a r) : radialHeightCutoff a r x = 1 := by
  have hnorm : ‖x - a‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
  apply Real.smoothTransition.one_of_one_le
  apply (one_le_div (by positivity : 0 < 3 * r ^ 2)).mpr
  nlinarith [norm_nonneg (x - a)]

lemma radialHeightCutoff_gradient_bound {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ K)
    (a x : Cover) {r : ℝ} (hr : 0 < r) :
    ‖fderiv ℝ (radialHeightCutoff a r) x‖ ≤ (4 * K / 3) / r := by
  have h := norm_fderiv_radialDensityWeight_bound hK hb a x
    (by positivity : 0 ≤ 2 * r) (by positivity : 0 < 3 * r ^ 2)
  convert! h using 1
  field_simp
  ring

lemma radialHeightCutoff_gradient_zero {a x : Cover} {r : ℝ} (hr : 0 < r)
    (hx : 2 * r ≤ ‖x - a‖) : fderiv ℝ (radialHeightCutoff a r) x = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  rw [radialHeightCutoff, fderiv_radialDensityWeight,
    radialDensitySlope_zero (by positivity) (by positivity) hx]
  simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def normalPlaneEmbedding (n : Cover) (y : Plane) : Cover :=
  normalProductChart n (0, WithLp.ofLp y)

lemma normalPlaneEmbedding_norm (n : Cover) (y : Plane) :
    ‖normalPlaneEmbedding n y‖ = ‖y‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [normalPlaneEmbedding, normalProductChart_apply, (normalRotation n).norm_map]
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]

lemma normalPlaneEmbedding_measurable (n : Cover) : Measurable (normalPlaneEmbedding n) :=
  (normalProductChart n).measurable.comp
    (measurable_const.prodMk (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.measurable)

lemma integral_plane_coordinates (n : Cover) (ψ : Cover → ℝ) :
    (∫ y : Fin 2 → ℝ, ψ (normalProductChart n (0, y))) =
      ∫ y : Plane, ψ (normalPlaneEmbedding n y) := by
  exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).integral_comp'
    (fun y : Fin 2 → ℝ ↦ ψ (normalProductChart n (0, y))) |>.symm

lemma plane_ball_real {s : ℝ} (hs : 0 ≤ s) :
    (volume : Measure Plane).real (Metric.ball 0 s) = Real.pi * s ^ 2 := by
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hs, ENNReal.toReal_ofReal Real.pi_pos.le]
  ring

lemma radialDensityWeight_plane_bound (n : Cover) {s ε : ℝ}
    (hs : 0 ≤ s) (hε : 0 < ε) (y : Plane) :
    ‖radialDensityWeight 0 s ε (normalPlaneEmbedding n y)‖ ≤
      (Metric.ball (0 : Plane) s).indicator (fun _ ↦ (1 : ℝ)) y := by
  by_cases hy : y ∈ Metric.ball (0 : Plane) s
  · rw [indicator_of_mem hy, Real.norm_eq_abs,
      abs_of_nonneg (radialDensityWeight_nonneg _ _ _ _)]
    exact radialDensityWeight_le_one _ _ _ _
  · rw [indicator_of_notMem hy]
    have hnorm : s ≤ ‖normalPlaneEmbedding n y - 0‖ := by
      simpa only [sub_zero, normalPlaneEmbedding_norm, Metric.mem_ball, dist_zero_right,
        not_lt] using hy
    rw [radialDensityWeight_zero hs hε hnorm, norm_zero]

lemma integral_radialDensityWeight_plane_tendsto (n : Cover) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun ε : ℝ ↦ ∫ y : Plane, radialDensityWeight 0 s ε (normalPlaneEmbedding n y))
      (𝓝[>] 0) (𝓝 (Real.pi * s ^ 2)) := by
  have hi : Integrable ((Metric.ball (0 : Plane) s).indicator (fun _ ↦ (1 : ℝ))) :=
    (integrableOn_const measure_ball_lt_top.ne).integrable_indicator Metric.isOpen_ball.measurableSet
  have ht := tendsto_integral_filter_of_dominated_convergence
    ((Metric.ball (0 : Plane) s).indicator (fun _ ↦ (1 : ℝ)))
    (Eventually.of_forall fun ε : ℝ ↦
      ((radialDensityWeight_contDiff 0 s ε).continuous.measurable.comp
        (normalPlaneEmbedding_measurable n)).aestronglyMeasurable)
    (show ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ y : Plane, ‖radialDensityWeight 0 s ε (normalPlaneEmbedding n y)‖ ≤
      (Metric.ball (0 : Plane) s).indicator (fun _ ↦ (1 : ℝ)) y from by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        exact Eventually.of_forall (radialDensityWeight_plane_bound n hs.le hε)) hi
    (Eventually.of_forall fun y : Plane ↦ radialDensityWeight_tendsto 0 (normalPlaneEmbedding n y) hs)
  have he : (fun y : Plane ↦ (Metric.ball (0 : Cover) s).indicator (fun _ ↦ (1 : ℝ))
      (normalPlaneEmbedding n y)) = (Metric.ball (0 : Plane) s).indicator (fun _ ↦ (1 : ℝ)) := by
    ext y
    have hy : normalPlaneEmbedding n y ∈ Metric.ball (0 : Cover) s ↔
        y ∈ Metric.ball (0 : Plane) s := by
      simp only [Metric.mem_ball, dist_zero_right, normalPlaneEmbedding_norm]
    by_cases h : y ∈ Metric.ball (0 : Plane) s
    · rw [indicator_of_mem h, indicator_of_mem (hy.mpr h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (mt hy.mp h)]
  have hval : (∫ y : Plane, (Metric.ball (0 : Plane) s).indicator (fun _ ↦ (1 : ℝ)) y) =
      Real.pi * s ^ 2 := by
    calc _ = (volume : Measure Plane).real (Metric.ball 0 s) :=
          integral_indicator_one Metric.isOpen_ball.measurableSet
         _ = _ := plane_ball_real hs.le
  rw [he, hval] at ht
  exact ht

end CubicTorus

end
end

end

end OAI
