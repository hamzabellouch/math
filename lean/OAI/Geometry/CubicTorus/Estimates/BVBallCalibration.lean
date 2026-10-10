import Mathlib
import OAI.Geometry.CubicTorus.Estimates.BVSharpUpperBound

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma admissible_latticePeriodize {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    (hb : ∀ x, ‖F x‖ ≤ 1) : AdmissibleField (latticePeriodize F) := by
  refine ⟨latticePeriodize_contDiff hF hc,latticePeriodize_periodic F,?_⟩
  intro x
  rw [← periodic_representative (latticePeriodize_periodic F) x,
    (latticePeriodize_eventuallyEq hc hs (fun i ↦
      ⟨(representative_mem_fundamentalCube _ i).1,(representative_mem_fundamentalCube _ i).2.le⟩)).eq_of_nhds]
  exact hb _

lemma radialDensityWeight_one_on_inner {a x : Cover} {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r < s) (hx : x ∈ Metric.closedBall a r) :
    radialDensityWeight a s (s^2-r^2) x = 1 := by
  have hn : ‖x-a‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
  apply Real.smoothTransition.one_of_one_le
  apply (one_le_div (by nlinarith : 0 < s^2-r^2)).mpr
  nlinarith [norm_nonneg (x-a)]

lemma radialDensityField_norm_le {a : Cover} {s ε : ℝ} (hs : 0 ≤ s) (hε : 0 < ε)
    (x : Cover) : ‖radialDensityField a s ε x‖ ≤ s := by
  by_cases hx : s ≤ ‖x-a‖
  · simp only [radialDensityField,radialDensityWeight_zero hs hε hx,zero_smul,norm_zero]
    exact hs
  · rw [radialDensityField,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (radialDensityWeight_nonneg _ _ _ _)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (radialDensityWeight_le_one _ _ _ _)).trans
      (le_of_not_ge hx)

lemma divergence_inner_radialDensityField {a x : Cover} {r s : ℝ}
    (hr : 0 < r) (hrs : r < s) (hx : x ∈ Metric.ball a r) :
    divergence (radialDensityField a s (s^2-r^2)) x = 3 := by
  have he : radialDensityField a s (s^2-r^2) =ᶠ[𝓝 x] (fun y : Cover ↦ y-a) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    rw [radialDensityField,radialDensityWeight_one_on_inner hr.le hrs (Metric.ball_subset_closedBall hy),one_smul]
  simp only [divergence,he.fderiv_eq]
  exact divergence_sub_const a x

def ballCalibration (r s : ℝ) (x : Cover) : Cover :=
  s⁻¹ • radialDensityField cubeCenter s (s^2-r^2) x

lemma ballCalibration_contDiff (r s : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (ballCalibration r s) :=
  (radialDensityField_contDiff _ _ _).const_smul _

lemma ballCalibration_compact {r s : ℝ} (hr : 0 < r) (hrs : r < s) :
    HasCompactSupport (ballCalibration r s) := by
  have hs0 : 0 ≤ s := (hr.trans hrs).le
  have hε : 0 < s^2-r^2 := by nlinarith
  change HasCompactSupport ((fun _ : Cover ↦ s⁻¹) • radialDensityField cubeCenter s (s^2-r^2))
  exact (radialDensityField_hasCompactSupport (a := cubeCenter) hs0 hε).smul_left

lemma ballCalibration_support {r s : ℝ} (hr : 0 < r) (hrs : r < s) (hs : s < 1/2) :
    tsupport (ballCalibration r s) ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  have hs0 : 0 ≤ s := (hr.trans hrs).le
  have hε : 0 < s^2-r^2 := by nlinarith
  exact (tsupport_smul_subset_right (fun _ : Cover ↦ s⁻¹)
    (radialDensityField cubeCenter s (s^2-r^2))).trans
    ((radialDensityField_tsupport hs0 hε).trans (cubeCenter_closedBall_interior hs))

lemma ballCalibration_norm {r s : ℝ} (hr : 0 < r) (hrs : r < s) (x : Cover) :
    ‖ballCalibration r s x‖ ≤ 1 := by
  have hs0 : 0 < s := hr.trans hrs
  have hε : 0 < s^2-r^2 := by nlinarith
  rw [ballCalibration,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs0)]
  exact (mul_le_mul_of_nonneg_left (radialDensityField_norm_le hs0.le hε x)
    (inv_nonneg.mpr hs0.le)).trans_eq (inv_mul_cancel₀ hs0.ne')

lemma ballCalibration_divergence {r s : ℝ} (hr : 0 < r) (hrs : r < s) (hs : s < 1/2)
    (x : Cover) (hx : x ∈ Metric.ball cubeCenter r) :
    divergence (latticePeriodize (ballCalibration r s)) x = 3/s := by
  have hm := coverBall_subset_cube (hrs.le.trans hs.le) hx
  have he := latticePeriodize_eventuallyEq (ballCalibration_compact hr hrs)
    (ballCalibration_support hr hrs hs) (fun i ↦ ⟨(hm i).1,(hm i).2.le⟩)
  change (∑ i : Fin 3, (fderiv ℝ (latticePeriodize (ballCalibration r s)) x
    (EuclideanSpace.single i 1)) i) = _
  rw [he.fderiv_eq]
  change divergence (fun y ↦ s⁻¹ • radialDensityField cubeCenter s (s^2-r^2) y) x = _
  rw [divergence_const_smul ((radialDensityField_contDiff _ _ _).differentiable (by simp) x) (s⁻¹),
    divergence_inner_radialDensityField hr hrs hx]
  ring

lemma integral_const_coverBall (r k : ℝ) (hr : 0 ≤ r) :
    (∫ _ in Metric.ball cubeCenter r, k ∂(volume : Measure Cover)) = k*(r^3*(Real.pi*4/3)) := by
  rw [integral_const]
  simp only [smul_eq_mul,measureReal_def,Measure.restrict_apply_univ,
    EuclideanSpace.volume_ball_fin_three,ENNReal.toReal_ofReal hr,
    ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]
  ring

lemma ball_calibration_flux_le {r s : ℝ} (hr : 0 < r) (hrs : r < s) (hs : s < 1/2) :
    ENNReal.ofReal (3/s * (r^3*(Real.pi*4/3))) ≤ perimeter (cubeBall r) := by
  have hp := admissible_latticePeriodize (ballCalibration_contDiff r s)
    (ballCalibration_compact hr hrs) (ballCalibration_support hr hrs hs) (ballCalibration_norm hr hrs)
  have hh : ENNReal.ofReal (∫ x in fundamentalCube ∩ quotientMap ⁻¹' cubeBall r,
      divergence (latticePeriodize (ballCalibration r s)) x) ≤ perimeter (cubeBall r) :=
    le_iSup_of_le _ (le_iSup_of_le hp le_rfl)
  rw [cubeBall_lift (hrs.le.trans hs.le)] at hh
  rwa [setIntegral_congr_fun Metric.isOpen_ball.measurableSet (ballCalibration_divergence hr hrs hs),
    integral_const_coverBall r (3/s) hr.le] at hh

theorem perimeter_cubeBall_eq {r : ℝ} (hr : 0 < r) (hs : r < 1/2) :
    perimeter (cubeBall r) = ENNReal.ofReal (4*Real.pi*r^2) := by
  apply le_antisymm
  · exact UpperComparison.perimeter_cubeBall_le hr hs.le
  · have hlim : Tendsto (fun s : ℝ ↦ ENNReal.ofReal (3/s*(r^3*(Real.pi*4/3)))) (𝓝[>] r)
        (𝓝 (ENNReal.ofReal (4*Real.pi*r^2))) := by
      have hl : Tendsto (fun s : ℝ ↦ 3/s*(r^3*(Real.pi*4/3))) (𝓝 r)
          (𝓝 (3/r*(r^3*(Real.pi*4/3)))) :=
        ((continuousAt_const.div continuousAt_id hr.ne').mul continuousAt_const).tendsto
      have hv : 3/r*(r^3*(Real.pi*4/3)) = 4*Real.pi*r^2 := by field_simp
      rw [hv] at hl
      exact (ENNReal.continuous_ofReal.tendsto _).comp (hl.mono_left nhdsWithin_le_nhds)
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hs)] with s hrs hs
    exact ball_calibration_flux_le hr hrs hs

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus.UpperComparison

lemma norm_axial_sub_center (x : Cover) :
    ‖axialProjection (x-cubeCenter)‖ = ‖discProjection x-discCenter‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_succ,axialProjection_zero,axialProjection_succ,norm_zero,
    zero_pow (by omega : 2 ≠ 0),zero_add,PiLp.sub_apply,discProjection_apply]
  rfl

lemma axial_sub_center_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Cover ↦ axialProjection (x-cubeCenter)) :=
  axialProjection.contDiff.comp (contDiff_id.sub contDiff_const)

def tubeCalibration (b : ContDiffBump (1/2 : ℝ)) (r s : ℝ) (x : Cover) : Cover :=
  s⁻¹ • (b (x 0) • radialDensityField 0 s (s^2-r^2) (axialProjection (x-cubeCenter)))

lemma tubeCalibration_contDiff (b : ContDiffBump (1/2 : ℝ)) (r s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (tubeCalibration b r s) := by
  have hb : ContDiff ℝ (⊤ : ℕ∞) (fun x : Cover ↦ b (x 0)) :=
    b.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).contDiff)
  exact (hb.smul ((radialDensityField_contDiff 0 s (s^2-r^2)).comp
    axial_sub_center_contDiff)).const_smul _

lemma tubeCalibration_norm (b : ContDiffBump (1/2 : ℝ)) {r s : ℝ}
    (hr : 0 < r) (hrs : r < s) (x : Cover) : ‖tubeCalibration b r s x‖ ≤ 1 := by
  have hs : 0 < s := hr.trans hrs
  have hε : 0 < s^2-r^2 := by nlinarith
  rw [tubeCalibration,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs),norm_smul,
    Real.norm_eq_abs,abs_of_nonneg b.nonneg]
  calc
    _ ≤ s⁻¹ * ‖radialDensityField 0 s (s^2-r^2) (axialProjection (x-cubeCenter))‖ :=
      mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) b.le_one) (inv_nonneg.mpr hs.le)
    _ ≤ s⁻¹*s := mul_le_mul_of_nonneg_left (radialDensityField_norm_le hs.le hε _) (inv_nonneg.mpr hs.le)
    _ = 1 := inv_mul_cancel₀ hs.ne'

lemma tubeCalibration_support (b : ContDiffBump (1/2 : ℝ)) {r s : ℝ}
    (hr : 0 < r) (hrs : r < s) :
    tsupport (tubeCalibration b r s) ⊆
      tubeSplit ⁻¹' (Metric.closedBall (1/2 : ℝ) b.rOut ×ˢ Metric.closedBall discCenter s) := by
  have hs : 0 ≤ s := (hr.trans hrs).le
  have hε : 0 < s^2-r^2 := by nlinarith
  apply closure_minimal _ ((Metric.isClosed_closedBall.prod Metric.isClosed_closedBall).preimage continuous_tubeSplit)
  intro x hx
  have hb : b (x 0) ≠ 0 := fun hz ↦ hx (by simp [tubeCalibration,hz])
  have hf : radialDensityField 0 s (s^2-r^2) (axialProjection (x-cubeCenter)) ≠ 0 :=
    fun hz ↦ hx (by simp only [tubeCalibration,hz,smul_zero])
  have hn := radialDensityField_tsupport hs hε (subset_tsupport _ hf)
  simp only [Metric.mem_closedBall,dist_zero_right] at hn
  refine ⟨Metric.ball_subset_closedBall (by rwa [← b.support_eq]),?_⟩
  simpa only [tubeSplit_apply,Metric.mem_closedBall,dist_eq_norm,norm_axial_sub_center] using hn

lemma tubeCalibration_compact (b : ContDiffBump (1/2 : ℝ)) {r s : ℝ}
    (hr : 0 < r) (hrs : r < s) : HasCompactSupport (tubeCalibration b r s) := by
  have hc : IsCompact (tubeSplit.symm '' (Metric.closedBall (1/2 : ℝ) b.rOut ×ˢ Metric.closedBall discCenter s)) :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image continuous_tubeSplit_symm
  apply hc.of_isClosed_subset isClosed_closure
  intro x hx
  exact ⟨tubeSplit x,tubeCalibration_support b hr hrs hx,tubeSplit.symm_apply_apply x⟩

lemma tubeCalibration_interior (b : ContDiffBump (1/2 : ℝ)) (hb : b.rOut < 1/2)
    {r s : ℝ} (hr : 0 < r) (hrs : r < s) (hs : s < 1/2) :
    tsupport (tubeCalibration b r s) ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  intro x hx i
  have hm := tubeCalibration_support b hr hrs hx
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · have hh : |x 0-1/2| ≤ b.rOut := by simpa only [Metric.mem_closedBall,Real.dist_eq,tubeSplit_apply] using hm.1
    rw [abs_le] at hh
    constructor <;> linarith
  · have hn : ‖discProjection x-discCenter‖ ≤ s := by simpa only [Metric.mem_closedBall,dist_eq_norm,tubeSplit_apply] using hm.2
    have hh := (PiLp.norm_apply_le (discProjection x-discCenter) j).trans hn
    change |x j.succ-1/2| ≤ s at hh
    rw [abs_le] at hh
    constructor <;> linarith

end CubicTorus.UpperComparison

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus.UpperComparison

lemma divergence_axial_sub_center (x : Cover) :
    divergence (fun y : Cover ↦ axialProjection (y-cubeCenter)) x = 2 := by
  have hf := axialProjection.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const cubeCenter)
  change HasFDerivAt (fun y : Cover ↦ axialProjection (y-cubeCenter)) axialProjection x at hf
  simp only [divergence,hf.fderiv]
  simp only [Fin.sum_univ_succ,axialProjection_zero,axialProjection_succ]
  norm_num [PiLp.single_apply]

lemma gradient_axialScalar_pair (b : ContDiffBump (1/2 : ℝ)) (x : Cover) :
    ⟪gradient (fun y : Cover ↦ b (y 0)) x,axialProjection (x-cubeCenter)⟫ = 0 := by
  rw [inner_gradient_left]
  change fderiv ℝ ((b : ℝ → ℝ) ∘ (EuclideanSpace.proj 0 : Cover →L[ℝ] ℝ)) x _ = _
  rw [fderiv_comp x ((b.contDiff : ContDiff ℝ (⊤ : ℕ∞) b).differentiable (by simp) (x 0))
    (EuclideanSpace.proj 0 : Cover →L[ℝ] ℝ).differentiableAt]
  simp only [ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply]
  change (fderiv ℝ (b : ℝ → ℝ) (x 0)) (axialProjection (x-cubeCenter) 0) = 0
  rw [axialProjection_zero,map_zero]

lemma tubeCalibration_divergence_inner (b : ContDiffBump (1/2 : ℝ)) {r s : ℝ}
    (hr : 0 < r) (hrs : r < s) (x : Cover) (hx : x ∈ coverTube r) :
    divergence (tubeCalibration b r s) x = (2/s)*b (x 0) := by
  have hn : ‖axialProjection (x-cubeCenter)‖ < r := by
    rw [norm_axial_sub_center]
    simpa only [Metric.mem_ball,dist_eq_norm,tubeSplit_apply] using hx.2
  have he : tubeCalibration b r s =ᶠ[𝓝 x]
      (fun y : Cover ↦ s⁻¹ • (b (y 0) • axialProjection (y-cubeCenter))) := by
    have hc := axial_sub_center_contDiff.continuous.norm
    filter_upwards [hc.continuousAt.eventually (Iio_mem_nhds hn)] with y hy
    rw [tubeCalibration,radialDensityField,
      radialDensityWeight_one_on_inner hr.le hrs (by simpa only [Metric.mem_closedBall,dist_zero_right] using hy.le),
      one_smul,sub_zero]
  have hbd : Differentiable ℝ (fun y : Cover ↦ b (y 0)) :=
    ((b.contDiff : ContDiff ℝ (⊤ : ℕ∞) b).comp (EuclideanSpace.proj 0 : Cover →L[ℝ] ℝ).contDiff).differentiable (by simp)
  simp only [divergence,he.fderiv_eq]
  change divergence (fun y : Cover ↦ s⁻¹ • (b (y 0) • axialProjection (y-cubeCenter))) x = _
  have hf : DifferentiableAt ℝ (fun y : Cover ↦ b (y 0) • axialProjection (y-cubeCenter)) x :=
    (hbd x).smul (axial_sub_center_contDiff.differentiable (by simp) x)
  rw [divergence_const_smul hf (s⁻¹),
    divergence_smul_function (hbd x) (axial_sub_center_contDiff.differentiable (by simp) x),
    divergence_axial_sub_center,gradient_axialScalar_pair]
  ring

lemma tubeCalibration_periodic_divergence (b : ContDiffBump (1/2 : ℝ)) (hb : b.rOut < 1/2)
    {r s : ℝ} (hr : 0 < r) (hrs : r < s) (hs : s < 1/2) (x : Cover) (hx : x ∈ coverTube r) :
    divergence (latticePeriodize (tubeCalibration b r s)) x = (2/s)*b (x 0) := by
  have hm := coverTube_subset_cube (hrs.le.trans hs.le) hx
  have he := latticePeriodize_eventuallyEq (tubeCalibration_compact b hr hrs)
    (tubeCalibration_interior b hb hr hrs hs) (fun i ↦ ⟨(hm i).1,(hm i).2.le⟩)
  simp only [divergence,he.fderiv_eq]
  exact tubeCalibration_divergence_inner b hr hrs x hx

lemma integral_axialScalar_coverTube {f : ℝ → ℝ} (hf : Continuous f) {r : ℝ} (hr : 0 ≤ r) :
    (∫ x in coverTube r, f (x 0)) = (∫ t in Ico (0 : ℝ) 1, f t)*(Real.pi*r^2) := by
  let g : ℝ × Plane → ℝ := fun p ↦ f p.1
  have hint : IntegrableOn (fun x : Cover ↦ f (x 0)) (coverTube r) :=
    (((hf.comp (EuclideanSpace.proj 0 : Cover →L[ℝ] ℝ).continuous).continuousOn.integrableOn_compact
      (isCompact_closure_coverTube r))).mono_set subset_closure
  have hi : IntegrableOn g (Ico (0 : ℝ) 1 ×ˢ Metric.ball discCenter r) volume := by
    rw [← tubeSplit_measurePreserving.integrableOn_comp_preimage tubeSplit.measurableEmbedding]
    simpa only [g,Function.comp_def,tubeSplit_apply,coverTube] using hint
  have he := tubeSplit_measurePreserving.setIntegral_preimage_emb tubeSplit.measurableEmbedding
    g (Ico (0 : ℝ) 1 ×ˢ Metric.ball discCenter r)
  change (∫ x in coverTube r, f (x 0)) = _ at he
  rw [he,Measure.volume_eq_prod,← Measure.prod_restrict]
  rw [IntegrableOn,Measure.volume_eq_prod,← Measure.prod_restrict] at hi
  rw [integral_prod g hi]
  simp only [g,integral_const,smul_eq_mul,measureReal_def,Measure.restrict_apply_univ,
    EuclideanSpace.volume_ball_fin_two,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr,ENNReal.toReal_ofReal Real.pi_pos.le,
    integral_const_mul]
  ring

lemma tube_calibration_flux_le (b : ContDiffBump (1/2 : ℝ)) (hb : b.rOut < 1/2)
    {r s : ℝ} (hr : 0 < r) (hrs : r < s) (hs : s < 1/2) :
    ENNReal.ofReal ((2/s)*((∫ t in Ico (0 : ℝ) 1, b t)*(Real.pi*r^2))) ≤ perimeter (cubeTube r) := by
  have hp := admissible_latticePeriodize (tubeCalibration_contDiff b r s)
    (tubeCalibration_compact b hr hrs) (tubeCalibration_interior b hb hr hrs hs) (tubeCalibration_norm b hr hrs)
  have hh : ENNReal.ofReal (∫ x in fundamentalCube ∩ quotientMap ⁻¹' cubeTube r,
      divergence (latticePeriodize (tubeCalibration b r s)) x) ≤ perimeter (cubeTube r) :=
    le_iSup_of_le _ (le_iSup_of_le hp le_rfl)
  rw [cubeTube_lift (hrs.le.trans hs.le)] at hh
  rwa [setIntegral_congr_fun (measurableSet_coverTube r) (tubeCalibration_periodic_divergence b hb hr hrs hs),
    integral_const_mul,integral_axialScalar_coverTube b.continuous hr.le] at hh

end CubicTorus.UpperComparison

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus.UpperComparison

def axialExhaustionBump (a : ℝ) (ha : 0 < a) (ha' : a < 1/2) : ContDiffBump (1/2 : ℝ) where
  rIn := a
  rOut := (a+1/2)/2
  rIn_pos := ha
  rIn_lt_rOut := by linarith

lemma axialExhaustionBump_outer {a : ℝ} (ha : 0 < a) (ha' : a < 1/2) :
    (axialExhaustionBump a ha ha').rOut < 1/2 := by
  change (a+1/2)/2 < 1/2
  linarith

lemma axialExhaustionBump_integral {a : ℝ} (ha : 0 < a) (ha' : a < 1/2) :
    2*a ≤ ∫ t in Ico (0 : ℝ) 1, axialExhaustionBump a ha ha' t := by
  let b := axialExhaustionBump a ha ha'
  have hi : IntegrableOn (b : ℝ → ℝ) (Ico 0 1) :=
    (b.continuous.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ico_subset_Icc_self
  have hsub : Metric.closedBall (1/2 : ℝ) a ⊆ Ico 0 1 := by
    intro t ht
    have hh : |t-1/2| ≤ a := by simpa only [Metric.mem_closedBall,Real.dist_eq] using ht
    rw [abs_le] at hh
    constructor <;> linarith
  have hlo := setIntegral_mono_set hi (Eventually.of_forall fun _ ↦ b.nonneg)
    (Eventually.of_forall hsub)
  have he : (∫ t in Metric.closedBall (1/2 : ℝ) a, b t) = 2*a := by
    have hpoint (t : ℝ) (ht : t ∈ Metric.closedBall (1/2 : ℝ) a) : b t = 1 :=
      b.one_of_mem_closedBall ht
    rw [setIntegral_congr_fun Metric.isClosed_closedBall.measurableSet hpoint,integral_const]
    simp only [smul_eq_mul,mul_one,measureReal_def,Measure.restrict_apply_univ,
      Real.volume_closedBall,ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*a)]
  exact he ▸ hlo

lemma tube_calibration_lower_fixed_radius {r s : ℝ} (hr : 0 < r) (hrs : r < s) (hs : s < 1/2) :
    ENNReal.ofReal ((2/s)*(Real.pi*r^2)) ≤ perimeter (cubeTube r) := by
  have hlim : Tendsto (fun a : ℝ ↦ ENNReal.ofReal ((2/s)*((2*a)*(Real.pi*r^2))))
      (𝓝[<] (1/2 : ℝ)) (𝓝 (ENNReal.ofReal ((2/s)*(Real.pi*r^2)))) := by
    have hc : Continuous (fun a : ℝ ↦ (2/s)*((2*a)*(Real.pi*r^2))) := by fun_prop
    have hl := (ENNReal.continuous_ofReal.comp hc).tendsto (1/2 : ℝ)
    norm_num only [Function.comp_apply,mul_one_div_cancel (by norm_num : (2 : ℝ) ≠ 0),one_mul] at hl
    exact hl.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1/2))] with a ha' ha
  have hb := tube_calibration_flux_le (axialExhaustionBump a ha ha')
    (axialExhaustionBump_outer ha ha') hr hrs hs
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hb
  have hs0 : 0 < s := hr.trans hrs
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (axialExhaustionBump_integral ha ha') (by positivity)) (by positivity)

theorem perimeter_cubeTube_eq {r : ℝ} (hr : 0 < r) (hs : r < 1/2) :
    perimeter (cubeTube r) = ENNReal.ofReal (2*Real.pi*r) := by
  apply le_antisymm (perimeter_cubeTube_le hr hs.le)
  have hlim : Tendsto (fun s : ℝ ↦ ENNReal.ofReal ((2/s)*(Real.pi*r^2)))
      (𝓝[>] r) (𝓝 (ENNReal.ofReal (2*Real.pi*r))) := by
    have hc : ContinuousAt (fun s : ℝ ↦ (2/s)*(Real.pi*r^2)) r :=
      (continuousAt_const.div continuousAt_id hr.ne').mul continuousAt_const
    have he : (2/r)*(Real.pi*r^2) = 2*Real.pi*r := by field_simp
    have hl := (ENNReal.continuous_ofReal.continuousAt.comp hc).tendsto
    change Tendsto _ (𝓝 r) (𝓝 (ENNReal.ofReal ((2/r)*(Real.pi*r^2)))) at hl
    rw [he] at hl
    exact hl.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hs)] with s hrs hs
  exact tube_calibration_lower_fixed_radius hr hrs hs

end CubicTorus.UpperComparison

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Pointwise
namespace CubicTorus

lemma latticeVector_injective : Function.Injective latticeVector := by
  intro n m h
  funext i
  have hi := congrArg (fun x : Cover ↦ x i) h
  change (n i : ℝ)=(m i : ℝ) at hi
  exact_mod_cast hi

instance latticeAddAction : AddAction (Fin 3 → ℤ) Cover where
  vadd n x := x+latticeVector n
  zero_vadd x := by change x+latticeVector 0=x; ext i; simp [latticeVector]
  add_vadd n m x := by
    change x+latticeVector (n+m)=(x+latticeVector m)+latticeVector n
    ext i; simp [latticeVector]; ring

instance latticeMeasurableVAdd : MeasurableConstVAdd (Fin 3 → ℤ) Cover where
  measurable_const_vadd shift :=
    show Measurable (fun point : Cover ↦ point+latticeVector shift) from
      measurable_id.add measurable_const

instance latticeVolumeInvariant : VAddInvariantMeasure (Fin 3 → ℤ) Cover volume where
  measure_preimage_vadd n s hs := by
    change volume ((fun x : Cover ↦ x+latticeVector n) ⁻¹' s)=volume s
    exact (measurePreserving_add_right volume (latticeVector n)).measure_preimage hs.nullMeasurableSet

lemma lattice_fundamentalCube : IsAddFundamentalDomain (Fin 3 → ℤ) fundamentalCube volume := by
  apply IsAddFundamentalDomain.mk' measurableSet_fundamentalCube.nullMeasurableSet
  intro x
  obtain ⟨n,hn⟩ := same_quotient_lattice (quotientMap_representative (quotientMap x))
  refine ⟨n,?_,?_⟩
  · change x+latticeVector n∈fundamentalCube
    rw [← hn]
    exact representative_mem_fundamentalCube _
  · intro m hm
    change x+latticeVector m∈fundamentalCube at hm
    have hq : quotientMap (x+latticeVector m)=quotientMap x := by
      rw [quotientMap_add,quotientMap_latticeVector,add_zero]
    have he : x+latticeVector m=x+latticeVector n := by
      rw [← hn,← hq,representative_quotientMap_of_mem hm]
    exact latticeVector_injective (add_left_cancel he)

lemma periodic_image_fundamental {T : Cover → Cover} (hc : Continuous T)
    (hb : Function.Bijective T)
    (hp : ∀ n x,T (x+latticeVector n)=T x+latticeVector n) :
    IsAddFundamentalDomain (Fin 3 → ℤ) (T '' fundamentalCube) volume := by
  apply IsAddFundamentalDomain.mk'
    ((hc.measurableEmbedding hb.1).measurableSet_image' measurableSet_fundamentalCube).nullMeasurableSet
  intro y
  obtain ⟨x,rfl⟩ := hb.2 y
  obtain ⟨n,hn,huniq⟩ : ∃! n : Fin 3 → ℤ,x+latticeVector n∈fundamentalCube := by
    obtain ⟨n,hn⟩ := same_quotient_lattice (quotientMap_representative (quotientMap x))
    refine ⟨n,?_,?_⟩
    · dsimp only; rw [← hn]; exact representative_mem_fundamentalCube _
    · intro m hm
      apply latticeVector_injective
      apply add_left_cancel (a:=x)
      rw [← hn,← (show quotientMap (x+latticeVector m)=quotientMap x by
        rw [quotientMap_add,quotientMap_latticeVector,add_zero]),representative_quotientMap_of_mem hm]
  refine ⟨n,?_,?_⟩
  · change T x+latticeVector n∈T '' fundamentalCube
    exact ⟨x+latticeVector n,hn,hp n x⟩
  · intro m hm
    obtain ⟨z,hz,hzm⟩ := hm
    exact huniq m (by dsimp only; have he : z=x+latticeVector m := hb.1 (hzm.trans (hp m x).symm); rwa [← he])

lemma integral_periodic_image_cube {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y] {T : Cover → Cover} (hc : Continuous T) (hb : Function.Bijective T)
    (hp : ∀ n x,T (x+latticeVector n)=T x+latticeVector n)
    {g : Cover → Y} (hg : ∀ n x,g (x+latticeVector n)=g x) :
    (∫ x in fundamentalCube,g x) = ∫ x in T '' fundamentalCube,g x :=
  lattice_fundamentalCube.setIntegral_eq (periodic_image_fundamental hc hb hp) hg

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinateMove_surjective (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x,‖fderiv ℝ f x‖₊≤M)
    {t : ℝ} (ht : |t| *M<1) : Function.Surjective (coordinateMove i f t) := by
  intro y
  let g : Cover → Cover := fun x ↦ y-(t*f x) • EuclideanSpace.single i 1
  have hg : ContractingWith (‖t‖₊*M) g := by
    refine ⟨by exact_mod_cast ht, LipschitzWith.of_dist_le_mul ?_⟩
    intro x z
    have he : g x-g z=(-(t*(f x-f z))) • EuclideanSpace.single i 1 := by dsimp [g]; module
    rw [dist_eq_norm,he,norm_smul]
    simp only [norm_neg,Real.norm_eq_abs,abs_mul,PiLp.norm_single,norm_one,mul_one,
      NNReal.coe_mul,coe_nnnorm]
    calc
      |t| * |f x-f z| ≤ |t| *(M*dist x z) := by
        exact mul_le_mul_of_nonneg_left (by simpa only [Real.dist_eq] using
          (lipschitzWith_of_nnnorm_fderiv_le hf hM).dist_le_mul x z) (abs_nonneg t)
      _ = _ := by ring
  refine ⟨hg.fixedPoint,?_⟩
  have he := hg.fixedPoint_isFixedPt
  change y-(t*f hg.fixedPoint) • EuclideanSpace.single i 1=hg.fixedPoint at he
  exact eq_sub_iff_add_eq.mp he.symm

def periodicCoordinateRegion (i : Fin 3) (f : Cover → ℝ) (t : ℝ) (E : Set Torus) : Set Torus :=
  representative ⁻¹' (coordinateMove i f t '' (quotientMap ⁻¹' E))

lemma periodicCoordinateRegion_measurable (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) {M : NNReal} (hM : ∀ x,‖fderiv ℝ f x‖₊≤M)
    {t : ℝ} (ht : |t| *M<1) {E : Set Torus} (hE : MeasurableSet E) :
    MeasurableSet (periodicCoordinateRegion i f t E) := by
  have hc : Continuous (coordinateMove i f t) := continuous_id.add
    ((continuous_const.mul hf.continuous).smul continuous_const)
  exact ((hc.measurableEmbedding (coordinateMove_injective i hf hM ht)).measurableSet_image'
    (measurable_quotientMap hE)).preimage measurable_representative

lemma periodicCoordinateRegion_lift (i : Fin 3) {f : Cover → ℝ}
    (hp : ∀ n x,f (x+latticeVector n)=f x) (t : ℝ) (E : Set Torus) :
    quotientMap ⁻¹' periodicCoordinateRegion i f t E=coordinateMove i f t '' (quotientMap ⁻¹' E) := by
  ext x
  have hind : ∀ n y, (y+latticeVector n∈coordinateMove i f t '' (quotientMap ⁻¹' E)) ↔
      y∈coordinateMove i f t '' (quotientMap ⁻¹' E) := by
    intro n y
    constructor
    · rintro ⟨z,hz,he⟩
      refine ⟨z+latticeVector (-n),?_,?_⟩
      · change quotientMap (z+latticeVector (-n))∈E
        simpa only [mem_preimage,quotientMap_add,quotientMap_latticeVector,add_zero] using hz
      · rw [coordinateMove_periodic i hp,he]
        ext j; simp [latticeVector]
    · rintro ⟨z,hz,rfl⟩
      refine ⟨z+latticeVector n,?_,coordinateMove_periodic i hp t n z⟩
      simpa only [mem_preimage,quotientMap_add,quotientMap_latticeVector,add_zero] using hz
  change representative (quotientMap x)∈coordinateMove i f t '' (quotientMap ⁻¹' E) ↔
    x∈coordinateMove i f t '' (quotientMap ⁻¹' E)
  obtain ⟨n,hn⟩ := same_quotient_lattice (quotientMap_representative (quotientMap x))
  rw [hn,hind]

lemma integral_periodicCoordinateRegion (i : Fin 3) {f : Cover → ℝ}
    (hf : Differentiable ℝ f) (hp : ∀ n x,f (x+latticeVector n)=f x)
    {M : NNReal} (hM : ∀ x,‖fderiv ℝ f x‖₊≤M) {t : ℝ} (ht : |t| *M<1)
    {E : Set Torus} (hE : MeasurableSet E) {g : Cover → ℝ}
    (hg : ∀ n x,g (x+latticeVector n)=g x) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' periodicCoordinateRegion i f t E,g x)=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,
        coordinateJacobian i f t x*g (coordinateMove i f t x) := by
  let S := quotientMap ⁻¹' periodicCoordinateRegion i f t E
  have hS : MeasurableSet S := measurable_quotientMap (periodicCoordinateRegion_measurable i hf hM ht hE)
  have hsp : ∀ n x,S.indicator g (x+latticeVector n)=S.indicator g x := by
    intro n x
    by_cases hx : x∈S
    · have hx' : x+latticeVector n∈S := by
        simpa only [S,mem_preimage,quotientMap_add,quotientMap_latticeVector,add_zero] using hx
      simp only [indicator_of_mem hx,indicator_of_mem hx',hg]
    · have hx' : x+latticeVector n∉S := by
        simpa only [S,mem_preimage,quotientMap_add,quotientMap_latticeVector,add_zero] using hx
      simp only [indicator_of_notMem hx,indicator_of_notMem hx']
  have hc : Continuous (coordinateMove i f t) := continuous_id.add
    ((continuous_const.mul hf.continuous).smul continuous_const)
  have he := integral_periodic_image_cube hc
    ⟨coordinateMove_injective i hf hM ht,coordinateMove_surjective i hf hM ht⟩
    (coordinateMove_periodic i hp t) hsp
  rw [integral_indicator hS,integral_indicator hS] at he
  simp only [Measure.restrict_restrict hS,inter_comm S] at he
  change (∫ x in fundamentalCube∩S,g x)=_
  rw [he]
  have him : coordinateMove i f t '' fundamentalCube∩S=
      coordinateMove i f t '' (fundamentalCube∩quotientMap ⁻¹' E) := by
    dsimp only [S]
    rw [periodicCoordinateRegion_lift i hp]
    exact (Set.image_inter (coordinateMove_injective i hf hM ht)).symm
  rw [him,integral_image_eq_integral_abs_det_fderiv_smul volume
    (measurableSet_fundamentalCube.inter (measurable_quotientMap hE))
    (fun x _ ↦ (coordinateMove_hasFDerivAt i (hf x) t).hasFDerivWithinAt)
    (coordinateMove_injective i hf hM ht).injOn]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [coordinateMoveDeriv_det,abs_of_pos (coordinateJacobian_pos i
    (fun y ↦ by exact_mod_cast hM y) ht x),smul_eq_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma perimeter_periodicCoordinateRegion_le (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) :
    perimeter (periodicCoordinateRegion i f t E) ≤
      ENNReal.ofReal (1 + 2 * |t| * M) * perimeter E := by
  have hfd := hf.differentiable (by simp)
  have hC : 0 < 1 + 2 * |t| * M := by positivity
  have hMr : ∀ x, ‖fderiv ℝ f x‖ ≤ (M : ℝ) := fun x ↦ by exact_mod_cast hM x
  unfold perimeter at ⊢
  refine iSup_le fun G ↦ iSup_le fun hG ↦ ?_
  rw [integral_periodicCoordinateRegion i hfd hp hM ht hE (divergence_periodic hG.2.1)]
  have hh := abs_flux_le_mul_perimeter hP
    (coordinatePullback_contDiff i hf t hG.1) (coordinatePullback_periodic i hp t hG.2.1)
    hC (coordinatePullback_norm_le i M.coe_nonneg hMr t hG.2.2)
  simp_rw [coordinatePullback_divergence i hf t hG.1] at hh
  calc
    _ ≤ ENNReal.ofReal ((1 + 2 * |t| * M) * (perimeter E).toReal) :=
      ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hh)
    _ = _ := by
      rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_toReal hP]
      rfl

lemma finitePerimeter_periodicCoordinateRegion (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ n x, f (x + latticeVector n) = f x)
    {M : NNReal} (hM : ∀ x, ‖fderiv ℝ f x‖₊ ≤ M)
    {t : ℝ} (ht : |t| * M < 1) {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E ≠ ⊤) : FinitePerimeter (periodicCoordinateRegion i f t E) := by
  refine ⟨(periodicCoordinateRegion_measurable i (hf.differentiable (by simp)) hM ht hE).nullMeasurableSet,
    (perimeter_periodicCoordinateRegion_le i hf hp hM ht hE hP).trans_lt ?_⟩
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hP.lt_top

namespace Periodic

structure Variation where
  coordinate : Fin 3
  function : Cover → ℝ
  bound : NNReal
  smooth : ContDiff ℝ (⊤ : ℕ∞) function
  periodic : ∀ n x,function (x+latticeVector n)=function x
  derivative_bound : ∀ x,‖fderiv ℝ function x‖₊≤bound

def Variation.ofWall (a : WallVariation) : Variation :=
  ⟨a.coordinate,a.function,a.bound,a.smooth,a.periodic,a.derivative_bound⟩

lemma exists_variation_of_function (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : ∀ n x,f (x+latticeVector n)=f x) :
    ∃ a : Variation,a.coordinate=i ∧ a.function=f := by
  obtain ⟨M,hM,hbound⟩ := periodic_bounded (hf.continuous_fderiv (by simp)) (fderiv_periodic hp)
  exact ⟨⟨i,f,⟨M,hM⟩,hf,hp,fun x ↦ by exact_mod_cast hbound x⟩,rfl,rfl⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

abbrev VariationChain := List (Variation × ℝ)

def chainMove : VariationChain → Cover → Cover
  | [],x => x
  | (a,t)::l,x => chainMove l (coordinateMove a.coordinate a.function t x)

def chainJacobian : VariationChain → Cover → ℝ
  | [],_ => 1
  | (a,t)::l,x => coordinateJacobian a.coordinate a.function t x *
      chainJacobian l (coordinateMove a.coordinate a.function t x)

def chainCofactor : VariationChain → Cover → Cover → Cover
  | [],_,n => n
  | (a,t)::l,x,n => chainCofactor l (coordinateMove a.coordinate a.function t x)
      (coordinateCofactor a.coordinate a.function t x n)

def chainPullback : VariationChain → (Cover → Cover) → Cover → Cover
  | [],F => F
  | (a,t)::l,F => coordinatePullback a.coordinate a.function t (chainPullback l F)

def chainRegion : VariationChain → Set Torus → Set Torus
  | [],E => E
  | (a,t)::l,E => chainRegion l (periodicCoordinateRegion a.coordinate a.function t E)

def ChainValid (l : VariationChain) : Prop := ∀ p∈l,|p.2| *(p.1.bound:ℝ)<1

def chainBound : VariationChain → ℝ
  | [] => 1
  | (a,t)::l => (1+2*|t| *(a.bound:ℝ))*chainBound l

lemma chainBound_pos (l : VariationChain) : 0<chainBound l := by
  induction l with
  | nil => norm_num [chainBound]
  | cons p l ih => rcases p with ⟨a,t⟩; exact mul_pos (by positivity) ih

lemma chainMove_contDiff (l : VariationChain) : ContDiff ℝ (⊤ : ℕ∞) (chainMove l) := by
  induction l with
  | nil => exact contDiff_id
  | cons p l ih => rcases p with ⟨a,t⟩; exact ih.comp (coordinateMove_contDiff a.coordinate a.smooth t)

lemma chainJacobian_contDiff (l : VariationChain) : ContDiff ℝ (⊤ : ℕ∞) (chainJacobian l) := by
  induction l with
  | nil => exact contDiff_const
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    exact (coordinateJacobian_contDiff a.coordinate a.smooth t).mul
      (ih.comp (coordinateMove_contDiff a.coordinate a.smooth t))

lemma chainPullback_contDiff (l : VariationChain) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : ContDiff ℝ (⊤ : ℕ∞) (chainPullback l F) := by
  induction l with
  | nil => exact hF
  | cons p l ih => rcases p with ⟨a,t⟩; exact coordinatePullback_contDiff a.coordinate a.smooth t ih

lemma chainPullback_periodic (l : VariationChain) {F : Cover → Cover}
    (hF : ∀ n x,F (x+latticeVector n)=F x) :
    ∀ n x,chainPullback l F (x+latticeVector n)=chainPullback l F x := by
  induction l with
  | nil => exact hF
  | cons p l ih => rcases p with ⟨a,t⟩; exact coordinatePullback_periodic a.coordinate a.periodic t ih

lemma chainPullback_norm (l : VariationChain) {F : Cover → Cover} (hF : ∀ x,‖F x‖≤1) :
    ∀ x,‖chainPullback l F x‖≤chainBound l := by
  induction l with
  | nil => exact hF
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    exact coordinatePullback_norm_le_mul a.coordinate a.bound.coe_nonneg
      (fun x ↦ by exact_mod_cast a.derivative_bound x) t (chainBound_pos l) ih

lemma chainPullback_divergence (l : VariationChain) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Cover) :
    divergence (chainPullback l F) x = chainJacobian l x * divergence F (chainMove l x) := by
  induction l generalizing x with
  | nil => simp [chainPullback,chainJacobian,chainMove]
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    rw [chainPullback,coordinatePullback_divergence a.coordinate a.smooth t (chainPullback_contDiff l hF),ih]
    simp only [chainJacobian,chainMove,mul_assoc]

lemma chain_inner_pullback (l : VariationChain) (F : Cover → Cover) (x n : Cover) :
    ⟪n,chainPullback l F x⟫=⟪chainCofactor l x n,F (chainMove l x)⟫ := by
  induction l generalizing x n with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    rw [chainPullback,inner_coordinatePullback,ih]
    rfl

lemma chainRegion_measurable {l : VariationChain} (hl : ChainValid l)
    {E : Set Torus} (hE : MeasurableSet E) : MeasurableSet (chainRegion l E) := by
  induction l generalizing E with
  | nil => exact hE
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    exact ih (fun p hp ↦ hl p (by simp [hp]))
      (periodicCoordinateRegion_measurable a.coordinate (a.smooth.differentiable (by simp))
        a.derivative_bound (hl (a,t) (by simp)) hE)

lemma chainRegion_finite {l : VariationChain} (hl : ChainValid l)
    {E : Set Torus} (hE : MeasurableSet E) (hfin : perimeter E<⊤) : FinitePerimeter (chainRegion l E) := by
  induction l generalizing E with
  | nil => exact ⟨hE.nullMeasurableSet,hfin⟩
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    have ht := hl (a,t) (by simp)
    exact ih (fun p hp ↦ hl p (by simp [hp]))
      (periodicCoordinateRegion_measurable a.coordinate (a.smooth.differentiable (by simp)) a.derivative_bound ht hE)
      (finitePerimeter_periodicCoordinateRegion a.coordinate a.smooth a.periodic a.derivative_bound ht hE hfin.ne).2

lemma chainMove_periodic (l : VariationChain) (n : Fin 3 → ℤ) (x : Cover) :
    chainMove l (x+latticeVector n)=chainMove l x+latticeVector n := by
  induction l generalizing x with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    rw [chainMove,coordinateMove_periodic a.coordinate a.periodic,ih]
    rfl

lemma chainJacobian_periodic (l : VariationChain) (n : Fin 3 → ℤ) (x : Cover) :
    chainJacobian l (x+latticeVector n)=chainJacobian l x := by
  induction l generalizing x with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    simp only [chainJacobian,coordinateMove_periodic a.coordinate a.periodic,ih,
      coordinateJacobian,fderiv_periodic a.periodic]

lemma integral_chainRegion {l : VariationChain} (hl : ChainValid l)
    {E : Set Torus} (hE : MeasurableSet E) {g : Cover → ℝ}
    (hg : ∀ n x,g (x+latticeVector n)=g x) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' chainRegion l E,g x)=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,chainJacobian l x*g (chainMove l x) := by
  induction l generalizing E with
  | nil => simp [chainRegion,chainJacobian,chainMove]
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    have ht := hl (a,t) (by simp)
    rw [chainRegion,ih (fun p hp ↦ hl p (by simp [hp]))
      (periodicCoordinateRegion_measurable a.coordinate (a.smooth.differentiable (by simp)) a.derivative_bound ht hE),
      integral_periodicCoordinateRegion a.coordinate (a.smooth.differentiable (by simp))
        a.periodic a.derivative_bound ht hE (fun n x ↦ by
          rw [chainJacobian_periodic,chainMove_periodic,hg])]
    simp only [chainJacobian,chainMove,mul_assoc]

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

abbrev VariationChain := List (WallVariation × ℝ)

def chainMove : VariationChain → Cover → Cover
  | [],x => x
  | (a,t)::l,x => chainMove l (coordinateMove a.coordinate a.function t x)

def chainJacobian : VariationChain → Cover → ℝ
  | [],_ => 1
  | (a,t)::l,x => coordinateJacobian a.coordinate a.function t x *
      chainJacobian l (coordinateMove a.coordinate a.function t x)

def chainCofactor : VariationChain → Cover → Cover → Cover
  | [],_,n => n
  | (a,t)::l,x,n => chainCofactor l (coordinateMove a.coordinate a.function t x)
      (coordinateCofactor a.coordinate a.function t x n)

def chainPullback : VariationChain → (Cover → Cover) → Cover → Cover
  | [],F => F
  | (a,t)::l,F => coordinatePullback a.coordinate a.function t (chainPullback l F)

def chainRegion : VariationChain → Set Torus → Set Torus
  | [],E => E
  | (a,t)::l,E => chainRegion l (coordinateRegion a.coordinate a.function t E)

def ChainValid (l : VariationChain) : Prop := ∀ p∈l,|p.2| *(p.1.bound:ℝ)<1

def chainBound : VariationChain → ℝ
  | [] => 1
  | (a,t)::l => (1+2*|t| *(a.bound:ℝ))*chainBound l

lemma chainBound_pos (l : VariationChain) : 0<chainBound l := by
  induction l with
  | nil => norm_num [chainBound]
  | cons p l ih => rcases p with ⟨a,t⟩; exact mul_pos (by positivity) ih

lemma chainMove_contDiff (l : VariationChain) : ContDiff ℝ (⊤ : ℕ∞) (chainMove l) := by
  induction l with
  | nil => exact contDiff_id
  | cons p l ih => rcases p with ⟨a,t⟩; exact ih.comp (coordinateMove_contDiff a.coordinate a.smooth t)

lemma chainJacobian_contDiff (l : VariationChain) : ContDiff ℝ (⊤ : ℕ∞) (chainJacobian l) := by
  induction l with
  | nil => exact contDiff_const
  | cons p l ih =>
    rcases p with ⟨a,t⟩
    exact (coordinateJacobian_contDiff a.coordinate a.smooth t).mul
      (ih.comp (coordinateMove_contDiff a.coordinate a.smooth t))

end CubicTorus
end
end
end

end OAI
