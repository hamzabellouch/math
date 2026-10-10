import Mathlib
import OAI.Geometry.CubicTorus.Regularity.BVTangentialBlowup

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma image_quotientMap_eq_preimage_representative {S : Set Cover}
    (hS : S ⊆ fundamentalCube) : quotientMap '' S = representative ⁻¹' S := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    change representative (quotientMap v) ∈ S
    rwa [representative_quotientMap_of_mem (hS hv)]
  · intro hx
    exact ⟨representative x, hx, quotientMap_representative x⟩

lemma torusVolume_quotientMap_image_cube {S : Set Cover} (hS : MeasurableSet S)
    (hc : S ⊆ fundamentalCube) : torusVolume (quotientMap '' S) = volume S := by
  have hi : MeasurableSet (quotientMap '' S) := by
    rw [image_quotientMap_eq_preimage_representative hc]
    exact hS.preimage measurable_representative
  rw [torusVolume, Measure.map_apply measurable_quotientMap hi,
    Measure.restrict_apply (hi.preimage measurable_quotientMap)]
  congr 1
  ext x
  constructor
  · rintro ⟨hx, hc'⟩
    rw [image_quotientMap_eq_preimage_representative hc] at hx
    change representative (quotientMap x) ∈ S at hx
    rwa [representative_quotientMap_of_mem hc'] at hx
  · intro hx
    exact ⟨⟨x, hx, rfl⟩, hc hx⟩

lemma haar_image_add_right {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd G] (μ : Measure G) [μ.IsAddRightInvariant] (a : G) (S : Set G) :
    μ ((fun x ↦ x + a) '' S) = μ S := by
  have he : (fun x ↦ x + a) '' S = (fun x ↦ x + (-a)) ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨x + (-a), hx, by simp⟩
  rw [he, measure_preimage_add_right]

lemma measurableSet_image_add_right {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd G] (a : G) {S : Set G} (hS : MeasurableSet S) :
    MeasurableSet ((fun x ↦ x + a) '' S) := by
  have he : (fun x ↦ x + a) '' S = (fun x ↦ x + (-a)) ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨x + (-a), hx, by simp⟩
  rw [he]
  exact hS.preimage (measurable_id.add_const _)

lemma image_quotientMap_eq_preimage_shortestLift {S : Set Cover}
    (hS : S ⊆ Metric.ball (0 : Cover) (1 / 2)) :
    quotientMap '' S = shortestLift ⁻¹' S := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    change shortestLift (quotientMap v) ∈ S
    rw [shortestLift_quotientMap (by simpa using hS hv)]
    exact hv
  · intro hx
    exact ⟨shortestLift x, hx, quotientMap_shortestLift x⟩

lemma torusVolume_quotientMap_image_local {S : Set Cover} (hS : MeasurableSet S)
    (hc : S ⊆ Metric.ball (0 : Cover) (1 / 2)) :
    torusVolume (quotientMap '' S) = volume S := by
  let T := (fun x : Cover ↦ x + cubeCenter) '' S
  have hT : MeasurableSet T := measurableSet_image_add_right _ hS
  have hTc : T ⊆ fundamentalCube := by
    rintro x ⟨v, hv, rfl⟩
    apply coverBall_subset_cube (le_refl (1 / 2 : ℝ))
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hc hv
  have he : quotientMap '' T = (fun x : Torus ↦ x + quotientMap cubeCenter) '' (quotientMap '' S) := by
    simp only [T, image_image, quotientMap_add]
  have hh := torusVolume_quotientMap_image_cube hT hTc
  rw [he, haar_image_add_right] at hh
  exact hh.trans (haar_image_add_right volume cubeCenter S)

lemma torusVolume_chart_image {S : Set Cover} (hS : MeasurableSet S)
    (hc : S ⊆ Metric.ball (0 : Cover) (1 / 2)) (c : Torus) :
    torusVolume ((fun v ↦ quotientMap v + c) '' S) = volume S := by
  rw [show (fun v ↦ quotientMap v + c) '' S =
    (fun x : Torus ↦ x + c) '' (quotientMap '' S) by rw [image_image],
    haar_image_add_right]
  exact torusVolume_quotientMap_image_local hS hc

lemma quotientMap_chart_image_ball (c : Torus) {r : ℝ} (hr : r ≤ 1 / 2) :
    (fun v ↦ quotientMap v + c) '' Metric.ball (0 : Cover) r = Metric.ball c r := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    change dist (quotientMap v + c) c < r
    rw [dist_eq_norm, add_sub_cancel_right, ← norm_shortestLift,
      shortestLift_quotientMap ((show ‖v‖ < r by simpa using hv).trans_le hr)]
    simpa using hv
  · intro hx
    refine ⟨shortestLift (x - c), ?_, ?_⟩
    · simpa only [Metric.mem_ball, dist_zero_right, norm_shortestLift, ← dist_eq_norm] using hx
    · simp only [quotientMap_shortestLift, sub_add_cancel]

lemma torusVolume_chart_map_restrict (c : Torus) {r : ℝ} (hr : r ≤ 1 / 2) :
    Measure.map (fun v ↦ quotientMap v + c) (volume.restrict (Metric.ball (0 : Cover) r)) =
      torusVolume.restrict (Metric.ball c r) := by
  have hm : Measurable (fun v ↦ quotientMap v + c) := measurable_quotientMap.add_const c
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hm hA, Measure.restrict_apply (hA.preimage hm), Measure.restrict_apply hA]
  rw [← torusVolume_chart_image ((hA.preimage hm).inter Metric.isOpen_ball.measurableSet)
    (fun _ hx ↦ Metric.ball_subset_ball hr hx.2) c]
  congr 1
  rw [inter_comm ((fun v ↦ quotientMap v + c) ⁻¹' A), Set.image_inter_preimage,
    quotientMap_chart_image_ball c hr, inter_comm]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

def radialDensityWeight (a : Cover) (r ε : ℝ) (x : Cover) : ℝ :=
  sublevelCutoff (fun y ↦ ‖y - a‖ ^ 2) (r ^ 2) ε x

def radialDensitySlope (a : Cover) (r ε : ℝ) (x : Cover) : ℝ :=
  deriv Real.smoothTransition ((r ^ 2 - ‖x - a‖ ^ 2) / ε) / ε

def radialDensityField (a : Cover) (r ε : ℝ) (x : Cover) : Cover :=
  radialDensityWeight a r ε x • (x - a)

lemma radialDensityWeight_contDiff (a : Cover) (r ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialDensityWeight a r ε) :=
  sublevelCutoff_contDiff ((contDiff_id.sub contDiff_const).norm_sq ℝ) _ _

lemma radialDensityField_contDiff (a : Cover) (r ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialDensityField a r ε) :=
  (radialDensityWeight_contDiff a r ε).smul (contDiff_id.sub contDiff_const)

lemma radialDensityWeight_nonneg (a : Cover) (r ε : ℝ) (x : Cover) :
    0 ≤ radialDensityWeight a r ε x := Real.smoothTransition.nonneg _

lemma radialDensitySlope_nonneg (a : Cover) (r : ℝ) {ε : ℝ} (hε : 0 < ε) (x : Cover) :
    0 ≤ radialDensitySlope a r ε x :=
  div_nonneg Real.smoothTransition.monotone.deriv_nonneg hε.le

lemma radialDensityWeight_zero {a x : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε)
    (hx : r ≤ ‖x - a‖) : radialDensityWeight a r ε x = 0 := by
  apply sublevelCutoff_eq_zero hε
  nlinarith

lemma radialDensitySlope_zero {a x : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε)
    (hx : r ≤ ‖x - a‖) : radialDensitySlope a r ε x = 0 := by
  unfold radialDensitySlope
  rw [smoothTransition_deriv_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by nlinarith) hε.le), zero_div]

lemma radialDensityField_tsupport {a : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    tsupport (radialDensityField a r ε) ⊆ Metric.closedBall a r := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hh
  have hzero := radialDensityWeight_zero hr hε (le_of_lt (by simpa only [Metric.mem_closedBall,
    dist_eq_norm, not_le] using hh))
  exact hx (by simp [radialDensityField, hzero])

lemma radialDensityField_hasCompactSupport {a : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    HasCompactSupport (radialDensityField a r ε) :=
  (isCompact_closedBall a r).of_isClosed_subset isClosed_closure (radialDensityField_tsupport hr hε)

lemma fderiv_norm_sq_sub (a x v : Cover) :
    fderiv ℝ (fun y : Cover ↦ ‖y - a‖ ^ 2) x v = 2 * ⟪x - a, v⟫ := by
  have h := ((hasFDerivAt_id x).sub_const a).norm_sq
  change HasFDerivAt (fun y : Cover ↦ ‖y - a‖ ^ 2) _ x at h
  rw [h.fderiv]
  simp [inner_sub_left]

lemma fderiv_radialDensityWeight (a x v : Cover) (r ε : ℝ) :
    fderiv ℝ (radialDensityWeight a r ε) x v =
      -2 * radialDensitySlope a r ε x * ⟪x - a, v⟫ := by
  have hq : DifferentiableAt ℝ (fun y : Cover ↦ ‖y - a‖ ^ 2) x :=
    ((((contDiff_id.sub contDiff_const).norm_sq ℝ) :
      ContDiff ℝ (⊤ : ℕ∞) (fun y : Cover ↦ ‖y - a‖ ^ 2)).differentiable (by simp)) x
  unfold radialDensityWeight
  rw [fderiv_sublevelCutoff hq]
  simp only [smul_apply, neg_apply, smul_eq_mul,
    fderiv_norm_sq_sub, radialDensitySlope]
  ring

lemma divergence_sub_const (a x : Cover) : divergence (fun y : Cover ↦ y - a) x = 3 := by
  rw [divergence, fderiv_sub_const a]
  simp [EuclideanSpace.single]

lemma tangentialDivergence_radialDensityField {n : Cover} (hn : ‖n‖ = 1)
    (a x : Cover) (r ε : ℝ) :
    tangentialDivergence (radialDensityField a r ε) x n =
      2 * radialDensityWeight a r ε x -
      2 * radialDensitySlope a r ε x * (‖x - a‖ ^ 2 - ⟪n, x - a⟫ ^ 2) := by
  have hf := ((radialDensityWeight_contDiff a r ε).differentiable (by simp)) x
  have hg : DifferentiableAt ℝ (fun y : Cover ↦ y - a) x := differentiableAt_id.sub_const a
  unfold tangentialDivergence radialDensityField
  rw [divergence_smul_function hf hg, divergence_sub_const, inner_gradient_left,
    fderiv_fun_smul hf hg, fderiv_sub_const a, fderiv_fun_id]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, ContinuousLinearMap.id_apply, inner_add_right,
    inner_smul_right, fderiv_radialDensityWeight, real_inner_self_eq_norm_sq, hn, one_pow,
    mul_one, real_inner_comm (x - a) n]
  ring

lemma radialDensityField_flux_bound {n : Cover} (hn : ‖n‖ = 1)
    (a x : Cover) {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    |⟪n, radialDensityField a r ε x⟫| ≤ r * radialDensityWeight a r ε x := by
  by_cases hxr : r ≤ ‖x - a‖
  · simp [radialDensityField, radialDensityWeight_zero hr hε hxr]
  · rw [radialDensityField, inner_smul_right, abs_mul,
      abs_of_nonneg (radialDensityWeight_nonneg a r ε x), mul_comm r]
    apply mul_le_mul_of_nonneg_left _ (radialDensityWeight_nonneg a r ε x)
    exact (abs_real_inner_le_norm n (x - a)).trans (by simpa only [hn, one_mul] using (le_of_not_ge hxr))

lemma radialDensityField_dilation_bound {n : Cover} (hn : ‖n‖ = 1)
    (a x : Cover) {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    2 * radialDensityWeight a r ε x ≤
      tangentialDivergence (radialDensityField a r ε) x n +
        2 * r ^ 2 * radialDensitySlope a r ε x := by
  rw [tangentialDivergence_radialDensityField hn]
  have hb := radialDensitySlope_nonneg a r hε x
  by_cases hxr : r ≤ ‖x - a‖
  · rw [radialDensitySlope_zero hr hε hxr]
    ring_nf
    rfl
  · have hnorm : ‖x - a‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg (x - a)]
    have hh := mul_le_mul_of_nonneg_left hnorm hb
    nlinarith [mul_nonneg hb (sq_nonneg ⟪n, x - a⟫)]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

def radialDensityMass (μ : FiniteMeasure NormalBundle) (a : Cover) (ε r : ℝ) : ℝ :=
  ∫ z, radialDensityWeight a r ε z.1 ∂(μ : Measure NormalBundle)

lemma continuous_radialDensitySlope (a : Cover) (r ε : ℝ) :
    Continuous (radialDensitySlope a r ε) := by
  apply Continuous.div_const
  exact (Real.smoothTransition.contDiff (n := (2 : ℕ∞))).continuous_deriv (by norm_num) |>.comp
    ((continuous_const.sub ((continuous_id.sub continuous_const).norm.pow 2)).div_const ε)

lemma integrable_radialDensityWeight (μ : FiniteMeasure NormalBundle) (a : Cover) (r ε : ℝ) :
    Integrable (fun z : NormalBundle ↦ radialDensityWeight a r ε z.1) (μ : Measure NormalBundle) :=
  ((radialDensityWeight_contDiff a r ε).continuous.comp
    (continuous_subtype_val.comp continuous_fst)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma integrable_radialDensitySlope (μ : FiniteMeasure NormalBundle) (a : Cover) (r ε : ℝ) :
    Integrable (fun z : NormalBundle ↦ radialDensitySlope a r ε z.1) (μ : Measure NormalBundle) :=
  ((continuous_radialDensitySlope a r ε).comp
    (continuous_subtype_val.comp continuous_fst)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma hasDerivAt_radialDensityWeight (a x : Cover) (r ε : ℝ) :
    HasDerivAt (fun s : ℝ ↦ radialDensityWeight a s ε x)
      (2 * r * radialDensitySlope a r ε x) r := by
  have ht := ((Real.smoothTransition.contDiff (n := (1 : ℕ∞))).differentiable (by norm_num)
    ((r ^ 2 - ‖x - a‖ ^ 2) / ε)).hasDerivAt
  have hq := (((hasDerivAt_id r).pow 2).sub_const (‖x - a‖ ^ 2)).div_const ε
  convert! ht.comp r hq using 1
  simp only [radialDensitySlope, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  ring

lemma hasDerivAt_radialDensityMass (μ : FiniteMeasure NormalBundle) (a : Cover)
    {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    HasDerivAt (radialDensityMass μ a ε)
      (∫ z, 2 * r * radialDensitySlope a r ε z.1 ∂(μ : Measure NormalBundle)) r := by
  obtain ⟨K, hK, hb⟩ := smoothTransition_exists_deriv_bound
  have hs : Ioo (r - 1) (r + 1) ∈ 𝓝 r := Ioo_mem_nhds (by linarith) (by linarith)
  have hm (s : ℝ) : AEStronglyMeasurable
      (fun z : NormalBundle ↦ radialDensityWeight a s ε z.1) (μ : Measure NormalBundle) :=
    (integrable_radialDensityWeight μ a s ε).aestronglyMeasurable
  have hm' : AEStronglyMeasurable
      (fun z : NormalBundle ↦ 2 * r * radialDensitySlope a r ε z.1) (μ : Measure NormalBundle) :=
    ((integrable_radialDensitySlope μ a r ε).const_mul _).aestronglyMeasurable
  have hb' : ∀ᵐ z ∂(μ : Measure NormalBundle), ∀ s ∈ Ioo (r - 1) (r + 1),
      ‖2 * s * radialDensitySlope a s ε z.1‖ ≤ 2 * (|r| + 1) * K / ε := by
    filter_upwards [] with z s hs
    have hsr : |s| ≤ |r| + 1 := by
      rw [abs_le]
      constructor <;> nlinarith [le_abs_self r, neg_abs_le r, hs.1, hs.2]
    have hsl : |radialDensitySlope a s ε z.1| ≤ K / ε := by
      simp only [radialDensitySlope, abs_div, abs_of_pos hε]
      exact div_le_div_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hb ((s ^ 2 - ‖(z.1 : Cover) - a‖ ^ 2) / ε)) hε.le
    simp only [Real.norm_eq_abs, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
    calc
      2 * |s| * |radialDensitySlope a s ε z.1| ≤ 2 * (|r| + 1) * (K / ε) :=
        mul_le_mul (by nlinarith) hsl (abs_nonneg _) (by positivity)
      _ = _ := by ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs (Eventually.of_forall hm)
    (integrable_radialDensityWeight μ a r ε) hm' hb' (integrable_const _)
    (Eventually.of_forall fun z s _ ↦ hasDerivAt_radialDensityWeight a z.1 s ε)).2

lemma radialDensityMass_nonneg (μ : FiniteMeasure NormalBundle) (a : Cover) (ε r : ℝ) :
    0 ≤ radialDensityMass μ a ε r :=
  integral_nonneg (fun _ ↦ radialDensityWeight_nonneg _ _ _ _)

theorem weakCMC_radialDensityMass_ode {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    (a : Cover) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hc : Metric.closedBall a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    (2 - |H| * r) * radialDensityMass μ a ε r ≤
      r * deriv (radialDensityMass μ a ε) r := by
  let F := radialDensityField a r ε
  have hf := radialDensityField_contDiff a r ε
  have hid := weakCMC_local_identity hμ hH hf (radialDensityField_hasCompactSupport hr.le hε)
    ((radialDensityField_tsupport hr.le hε).trans hc)
  have ht : Integrable (fun z : NormalBundle ↦ tangentialDivergence F z.1 z.2)
      (μ : Measure NormalBundle) :=
    (continuous_tangentialDivergence hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfl : Integrable (fun z : NormalBundle ↦ ⟪(z.2 : Cover), F z.1⟫)
      (μ : Measure NormalBundle) :=
    (continuous_normalUnit.inner (hf.continuous.comp
      (continuous_subtype_val.comp continuous_fst))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hw := integrable_radialDensityWeight μ a r ε
  have hs := integrable_radialDensitySlope μ a r ε
  have hbound := integral_mono (hw.const_mul 2) (ht.add (hs.const_mul (2 * r ^ 2)))
    (fun z : NormalBundle ↦ radialDensityField_dilation_bound z.2.property a z.1 hr.le hε)
  simp only [Pi.add_apply] at hbound
  rw [integral_const_mul, integral_add ht (hs.const_mul _), integral_const_mul] at hbound
  change 2 * radialDensityMass μ a ε r ≤
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) +
      2 * r ^ 2 * ∫ z, radialDensitySlope a r ε z.1 ∂(μ : Measure NormalBundle) at hbound
  rw [hid] at hbound
  have hfb : |∫ z, ⟪(z.2 : Cover), F z.1⟫ ∂(μ : Measure NormalBundle)| ≤
      r * radialDensityMass μ a ε r := by
    calc
      _ ≤ ∫ z, |⟪(z.2 : Cover), F z.1⟫| ∂(μ : Measure NormalBundle) := abs_integral_le_integral_abs
      _ ≤ ∫ z, r * radialDensityWeight a r ε z.1 ∂(μ : Measure NormalBundle) :=
        integral_mono hfl.abs (hw.const_mul _)
          (fun z : NormalBundle ↦ radialDensityField_flux_bound z.2.property a z.1 hr.le hε)
      _ = _ := integral_const_mul _ _
  have hflux : H * (∫ z, ⟪(z.2 : Cover), F z.1⟫ ∂(μ : Measure NormalBundle)) ≤
      |H| * r * radialDensityMass μ a ε r := by
    calc
      _ ≤ |H * (∫ z, ⟪(z.2 : Cover), F z.1⟫ ∂(μ : Measure NormalBundle))| := le_abs_self _
      _ = |H| * |∫ z, ⟪(z.2 : Cover), F z.1⟫ ∂(μ : Measure NormalBundle)| := abs_mul _ _
      _ ≤ |H| * (r * radialDensityMass μ a ε r) := mul_le_mul_of_nonneg_left hfb (abs_nonneg _)
      _ = _ := by ring
  rw [(hasDerivAt_radialDensityMass μ a hε r).deriv, integral_const_mul]
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open Set
open scoped Topology
namespace CubicTorus

lemma hasDerivAt_cmcDensityRatio {m : ℝ → ℝ} {d r k : ℝ} (hr : 0 < r)
    (hm : HasDerivAt m d r) :
    HasDerivAt (fun t : ℝ ↦ Real.exp (k * t) * m t / t ^ 2)
      (Real.exp (k * r) / r ^ 3 * (r * d + (k * r - 2) * m r)) r := by
  have he := ((hasDerivAt_id r).const_mul k).exp
  have hd := (hasDerivAt_id r).pow 2
  convert! (he.mul hm).div hd (by exact pow_ne_zero 2 hr.ne') using 1
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, Pi.pow_apply, Pi.mul_apply]
  field_simp [hr.ne']
  ring

theorem cmcDensityRatio_monotoneOn {m d : ℝ → ℝ} {k R : ℝ}
    (hd : ∀ r ∈ Ioc 0 R, HasDerivAt m (d r) r)
    (hode : ∀ r ∈ Ioc 0 R, (2 - k * r) * m r ≤ r * d r) :
    MonotoneOn (fun r : ℝ ↦ Real.exp (k * r) * m r / r ^ 2) (Ioc 0 R) := by
  have hh (r : ℝ) (hr : r ∈ Ioc 0 R) := hasDerivAt_cmcDensityRatio hr.1 (hd r hr)
    (k := k)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 R)
    (fun r hr ↦ (hh r hr).continuousAt.continuousWithinAt)
    (fun r hr ↦ (hh r (interior_subset hr)).hasDerivWithinAt)
  intro r hr
  have hr' : r ∈ Ioc 0 R := interior_subset hr
  apply mul_nonneg (div_nonneg (Real.exp_pos _).le (pow_nonneg hr'.1.le _))
  have h := hode r hr'
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

def cellBallMass (μ : FiniteMeasure NormalBundle) (a : Cover) (r : ℝ) : ℝ :=
  (μ : Measure NormalBundle).real {z | (z.1 : Cover) ∈ Metric.ball a r}

lemma measurableSet_cellBall (a : Cover) (r : ℝ) :
    MeasurableSet {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r} :=
  Metric.isOpen_ball.measurableSet.preimage (measurable_subtype_coe.comp measurable_fst)

lemma radialDensityWeight_tendsto (a x : Cover) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun ε : ℝ ↦ radialDensityWeight a r ε x) (𝓝[>] 0)
      (𝓝 ((Metric.ball a r).indicator (fun _ : Cover ↦ (1 : ℝ)) x)) := by
  by_cases hx : x ∈ Metric.ball a r
  · have hxr : ‖x - a‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    have hp : 0 < r ^ 2 - ‖x - a‖ ^ 2 := by nlinarith [norm_nonneg (x - a)]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hp)] with ε hε hεδ
    rw [indicator_of_mem hx]
    exact (Real.smoothTransition.one_of_one_le ((one_le_div hε).2 (by simpa using hεδ.le))).symm
  · have hxr : r ≤ ‖x - a‖ := by simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hx
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [indicator_of_notMem hx]
    exact (radialDensityWeight_zero hr.le hε hxr).symm

lemma radialDensityMass_tendsto (μ : FiniteMeasure NormalBundle) (a : Cover)
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun ε : ℝ ↦ radialDensityMass μ a ε r) (𝓝[>] 0) (𝓝 (cellBallMass μ a r)) := by
  have hm (ε : ℝ) := (integrable_radialDensityWeight μ a r ε).aestronglyMeasurable
  have hb (ε : ℝ) : ∀ᵐ z ∂(μ : Measure NormalBundle), ‖radialDensityWeight a r ε z.1‖ ≤ (1 : ℝ) := by
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (radialDensityWeight_nonneg _ _ _ _)]
    exact Real.smoothTransition.le_one _
  have ht := tendsto_integral_filter_of_dominated_convergence (fun _ : NormalBundle ↦ (1 : ℝ))
    (Eventually.of_forall hm) (Eventually.of_forall hb) (integrable_const _)
    (Eventually.of_forall fun z : NormalBundle ↦ radialDensityWeight_tendsto a z.1 hr)
  have he : (fun z : NormalBundle ↦ (Metric.ball a r).indicator (fun _ : Cover ↦ (1 : ℝ)) z.1) =
      {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r}.indicator 1 := by
    ext z
    by_cases hz : (z.1 : Cover) ∈ Metric.ball a r
    · rw [indicator_of_mem hz, indicator_of_mem
        (show z ∈ {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r} from hz)]
      rfl
    · rw [indicator_of_notMem hz, indicator_of_notMem
        (show z ∉ {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r} from hz)]
  rwa [he, integral_indicator_one (measurableSet_cellBall a r)] at ht

lemma weakCMC_radialDensityMass_monotone {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    (a : Cover) {ε R : ℝ} (hε : 0 < ε)
    (hc : Metric.closedBall a R ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    MonotoneOn (fun r : ℝ ↦ Real.exp (|H| * r) * radialDensityMass μ a ε r / r ^ 2) (Ioc 0 R) := by
  apply cmcDensityRatio_monotoneOn
    (d := fun r ↦ deriv (radialDensityMass μ a ε) r)
  · intro r _
    exact (hasDerivAt_radialDensityMass μ a hε r).differentiableAt.hasDerivAt
  · intro r hr
    exact weakCMC_radialDensityMass_ode hμ hH a hr.1 hε
      ((Metric.closedBall_subset_closedBall hr.2).trans hc)

theorem weakCMC_cellBallMass_monotone {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    (a : Cover) {R : ℝ}
    (hc : Metric.closedBall a R ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    MonotoneOn (fun r : ℝ ↦ Real.exp (|H| * r) * cellBallMass μ a r / r ^ 2) (Ioc 0 R) := by
  intro r hr s hs hrs
  have hlr := ((radialDensityMass_tendsto μ a hr.1).const_mul (Real.exp (|H| * r))).div_const (r ^ 2)
  have hls := ((radialDensityMass_tendsto μ a hs.1).const_mul (Real.exp (|H| * s))).div_const (s ^ 2)
  apply le_of_tendsto_of_tendsto hlr hls
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact weakCMC_radialDensityMass_monotone hμ hH a hε hc hr hs hrs

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma quotientMap_injective_open_closed_cell {x y : Cover}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hy : ∀ i, 0 < y i ∧ y i < 1)
    (he : quotientMap x = quotientMap y) : x = y := by
  obtain ⟨n, hn⟩ := same_quotient_lattice he
  have hz (i : Fin 3) : n i = 0 := by
    have he' := congrArg (fun z : Cover ↦ z i) hn
    change x i = y i + (n i : ℝ) at he'
    have hlt : (n i : ℝ) < 1 := by linarith [(hx i).2, (hy i).1]
    have hgt : (-1 : ℝ) < (n i : ℝ) := by linarith [(hx i).1, (hy i).2]
    have hlt' : n i < (1 : ℤ) := by exact_mod_cast hlt
    have hgt' : (-1 : ℤ) < n i := by exact_mod_cast hgt
    omega
  rw [show n = 0 from funext hz, latticeVector_zero, add_zero] at hn
  exact hn

lemma quotientMap_image_ball (a : Cover) (r : ℝ) :
    quotientMap '' Metric.ball a r = Metric.ball (quotientMap a) r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change dist (quotientMap y) (quotientMap a) < r
    rw [dist_eq_norm, ← quotientMap_sub]
    exact (norm_quotientMap_le _).trans_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hy)
  · intro hx
    refine ⟨shortestLift (x - quotientMap a) + a, ?_, ?_⟩
    · simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, norm_shortestLift] using hx
    · rw [quotientMap_add, quotientMap_shortestLift, sub_add_cancel]

lemma compactCell_mem_quotient_ball_iff (z : CompactCell) (a : Cover) (r : ℝ)
    (hc : Metric.ball a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    quotientMap z ∈ Metric.ball (quotientMap a) r ↔ (z : Cover) ∈ Metric.ball a r := by
  constructor
  · intro hz
    rw [← quotientMap_image_ball a r] at hz
    obtain ⟨y, hy, he⟩ := hz
    have he' := quotientMap_injective_open_closed_cell (compactCell_coordinates z) (hc hy) he.symm
    rwa [he']
  · intro hz
    rw [← quotientMap_image_ball a r]
    exact ⟨z, hz, rfl⟩

lemma cellBallMass_eq_spatialNormalMeasure (μ : FiniteMeasure NormalBundle) (a : Cover) (r : ℝ)
    (hc : Metric.ball a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    cellBallMass μ a r = (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap a) r) := by
  unfold cellBallMass
  change _ = (Measure.map normalProjection (μ : Measure NormalBundle) (Metric.ball (quotientMap a) r)).toReal
  rw [Measure.map_apply normalProjection_continuous.measurable Metric.isOpen_ball.measurableSet]
  congr 1
  ext z
  exact (compactCell_mem_quotient_ball_iff z.1 a r hc).symm

theorem weakCMC_spatial_ball_monotone {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    (a : Cover) {R : ℝ}
    (hc : Metric.closedBall a R ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    MonotoneOn (fun r : ℝ ↦ Real.exp (|H| * r) *
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap a) r) / r ^ 2) (Ioc 0 R) := by
  apply (weakCMC_cellBallMass_monotone hμ hH a hc).congr
  intro r hr
  dsimp only
  rw [cellBallMass_eq_spatialNormalMeasure μ a r
    ((Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hr.2)).trans hc)]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma exists_density_of_cmc_monotone {m : ℝ → ℝ} {k R : ℝ} (hR : 0 < R)
    (hm : ∀ r ∈ Ioc 0 R, 0 ≤ m r)
    (hmono : MonotoneOn (fun r : ℝ ↦ Real.exp (k * r) * m r / r ^ 2) (Ioc 0 R)) :
    ∃ θ : ℝ, 0 ≤ θ ∧ Tendsto (fun r : ℝ ↦ m r / r ^ 2) (𝓝[>] 0) (𝓝 θ) := by
  let f : ℝ → ℝ := fun r ↦ Real.exp (k * r) * m r / r ^ 2
  have hne : (Ioo (0 : ℝ) R).Nonempty := nonempty_Ioo.mpr hR
  have hb : BddBelow (f '' Ioo 0 R) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (hm r ⟨hr.1, hr.2.le⟩)) (sq_nonneg _)
  have hf := (hmono.mono Ioo_subset_Ioc_self).tendsto_nhdsWithin_Ioo_right hne hb
  have he : Tendsto (fun r : ℝ ↦ Real.exp (k * r)) (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
    have hc : Continuous (fun r : ℝ ↦ Real.exp (k * r)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  refine ⟨sInf (f '' Ioo 0 R), ?_, ?_⟩
  · exact le_csInf (hne.image _) (by
      rintro _ ⟨r, hr, rfl⟩
      exact div_nonneg (mul_nonneg (Real.exp_pos _).le (hm r ⟨hr.1, hr.2.le⟩)) (sq_nonneg _))
  · have hh := hf.div he (by norm_num : (1 : ℝ) ≠ 0)
    have heq : (fun r : ℝ ↦ f r / Real.exp (k * r)) = (fun r : ℝ ↦ m r / r ^ 2) := by
      ext r
      dsimp only [f]
      rw [mul_div_assoc, mul_div_cancel_left₀ _ (Real.exp_ne_zero _)]
    change Tendsto (fun r : ℝ ↦ f r / Real.exp (k * r)) (𝓝[>] 0)
      (𝓝 (sInf (f '' Ioo 0 R) / 1)) at hh
    rwa [heq, div_one] at hh

theorem weakCMC_exists_spatial_density {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    (a : Cover) {R : ℝ} (hR : 0 < R)
    (hc : Metric.closedBall a R ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    ∃ θ : ℝ, 0 ≤ θ ∧ Tendsto
      (fun r : ℝ ↦ (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap a) r) / r ^ 2)
      (𝓝[>] 0) (𝓝 θ) :=
  exists_density_of_cmc_monotone hR (fun _ _ ↦ ENNReal.toReal_nonneg)
    (weakCMC_spatial_ball_monotone hμ hH a hc)

lemma isMinimizerAt_density_pos {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {a : Torus} (ha : a ∈ frontier (openRepresentative E)) {θ : ℝ}
    (hθ : Tendsto (fun r : ℝ ↦
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball a r) / r ^ 2)
      (𝓝[>] 0) (𝓝 θ)) : 0 < θ := by
  obtain ⟨R, c, hR, hc, hd⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  rw [isMinimizerAt_frontier_openRepresentative hV hE hmin] at ha
  apply hc.trans_le
  apply ge_of_tendsto hθ
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hR)] with r hr hrR
  exact (le_div_iff₀ (sq_pos_of_pos hr)).mpr (hd μ hμ a ha r hr hrR.le)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem exists_positive_wallVariation_smallShift {E : Set Torus} (hE : MeasurableSet E)
    (hP : 0 < perimeter E) :
    ∃ (a : Cover) (D : WallVariation),
      (a = 0 ∨ ∃ i : Fin 3, a = (1 / 2 : ℝ) • EuclideanSpace.single i 1) ∧
      0 < directionalFlux ((fun z ↦ z + quotientMap a) ⁻¹' E) D.coordinate D.function := by
  obtain ⟨i, f, hf, hp, hflux⟩ := exists_positive_directionalFlux hP
  let f₀ : Cover → ℝ := fun x ↦ wallCutoff i x * f x
  let f₁ : Cover → ℝ := fun x ↦ (1 - wallCutoff i x) * f x
  have hc₀ : ContDiff ℝ (⊤ : ℕ∞) f₀ := (wallCutoff_contDiff i).mul hf
  have hc₁ : ContDiff ℝ (⊤ : ℕ∞) f₁ := (contDiff_const.sub (wallCutoff_contDiff i)).mul hf
  have hp₀ : ∀ n x, f₀ (x + latticeVector n) = f₀ x := by
    intro n x
    dsimp only [f₀]
    rw [wallCutoff_periodic, hp]
  have hp₁ : ∀ n x, f₁ (x + latticeVector n) = f₁ x := by
    intro n x
    dsimp only [f₁]
    rw [wallCutoff_periodic, hp]
  have he : (fun x ↦ f₀ x + f₁ x) = f := by
    funext x
    dsimp only [f₀, f₁]
    ring
  have hs : 0 < directionalFlux E i f₀ + directionalFlux E i f₁ := by
    rw [← directionalFlux_add E i hc₀ hc₁, he]
    exact hflux
  by_cases hpos : 0 < directionalFlux E i f₀
  · have hface₀ : ∀ x, x i = 0 ∨ x i = 1 → f₀ x = 0 := by
      intro x hx
      simp [f₀, wallCutoff_face i x hx]
    obtain ⟨D, hi, hfD⟩ := exists_wallVariation_of_function i hc₀ hp₀ hface₀
    refine ⟨0, D, Or.inl rfl, ?_⟩
    have hz : quotientMap 0 = 0 := by ext j; simp [quotientMap]
    simpa only [hi, hfD, hz, add_zero, preimage_id'] using hpos
  · have hpos₁ : 0 < directionalFlux E i f₁ := by linarith
    let a : Cover := (1 / 2 : ℝ) • EuclideanSpace.single i 1
    let g : Cover → ℝ := fun x ↦ f₁ (x + a)
    have hgc : ContDiff ℝ (⊤ : ℕ∞) g := hc₁.comp (contDiff_id.add contDiff_const)
    have hgp : ∀ n x, g (x + latticeVector n) = g x := by
      intro n x
      dsimp only [g]
      rw [add_right_comm, hp₁]
    have hgf : ∀ x, x i = 0 ∨ x i = 1 → g x = 0 := by
      intro x hx
      dsimp only [g, f₁, a]
      rw [wallCutoff_halfShift, wallCutoff_face i x hx]
      ring
    obtain ⟨D, hi, hfD⟩ := exists_wallVariation_of_function i hgc hgp hgf
    refine ⟨a, D, Or.inr ⟨i, rfl⟩, ?_⟩
    rw [hi, hfD]
    change 0 < directionalFlux ((fun z ↦ z + quotientMap a) ⁻¹' E) i (fun x ↦ f₁ (x + a))
    rwa [directionalFlux_translation i hc₁ hp₁ a hE]

end CubicTorus

namespace CubicTorus

def quarterCenter : Cover := WithLp.toLp 2 (fun _ ↦ (1 / 4 : ℝ))

lemma smallShift_coordinates {a : Cover}
    (ha : a = 0 ∨ ∃ i : Fin 3, a = (1 / 2 : ℝ) • EuclideanSpace.single i 1) (j : Fin 3) :
    a j = 0 ∨ a j = 1 / 2 := by
  rcases ha with rfl | ⟨i, rfl⟩
  · exact Or.inl rfl
  · by_cases hji : j = i
    · subst j
      right
      simp
    · left
      simp [hji]

lemma smallShift_double_quotient {a : Cover}
    (ha : a = 0 ∨ ∃ i : Fin 3, a = (1 / 2 : ℝ) • EuclideanSpace.single i 1) :
    quotientMap (a + a) = 0 := by
  rcases ha with rfl | ⟨i, rfl⟩
  · ext j; simp [quotientMap]
  · have he : (1 / 2 : ℝ) • EuclideanSpace.single i 1 + (1 / 2 : ℝ) • EuclideanSpace.single i 1 =
        latticeVector (fun j ↦ if j = i then 1 else 0) := by
      ext j
      by_cases hj : j = i
      · subst j
        norm_num [latticeVector]
      · simp [latticeVector, hj]
    rw [he, quotientMap_latticeVector]

lemma smallShift_center_ball {a : Cover}
    (ha : a = 0 ∨ ∃ i : Fin 3, a = (1 / 2 : ℝ) • EuclideanSpace.single i 1) :
    Metric.closedBall (quarterCenter + a) (1 / 8) ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  intro x hx j
  have hb := (PiLp.norm_apply_le (x - (quarterCenter + a)) j).trans
    (show ‖x - (quarterCenter + a)‖ ≤ (1 / 8 : ℝ) from hx)
  simp only [PiLp.sub_apply, PiLp.add_apply, quarterCenter, Real.norm_eq_abs] at hb
  rcases smallShift_coordinates ha j with hj | hj
  · rw [hj] at hb
    have hh := abs_le.mp hb
    constructor <;> linarith
  · rw [hj] at hb
    have hh := abs_le.mp hb
    constructor <;> linarith

theorem isMinimizerAt_exists_centered_weakCMC {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) (hE : MeasurableSet E) (c : Torus) :
    ∃ (b d : Cover) (μ : FiniteMeasure NormalBundle) (H : ℝ),
      quotientMap (d + b) = c ∧
      Metric.closedBall d (1 / 8) ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} ∧
      IsNormalMeasure ((fun z ↦ z + quotientMap b) ⁻¹' E) μ ∧
      ∀ D : WallVariation, normalFirstVariation μ D =
        H * directionalFlux ((fun z ↦ z + quotientMap b) ⁻¹' E) D.coordinate D.function := by
  let b₀ := shortestLift c - quarterCenter
  let E₀ := (fun z ↦ z + quotientMap b₀) ⁻¹' E
  have hE₀ : MeasurableSet E₀ := hE.preimage (continuous_id.add continuous_const).measurable
  have hm₀ : IsMinimizerAt V E₀ := isMinimizerAt_translation hmin _
  obtain ⟨a, D, ha, hD⟩ := exists_positive_wallVariation_smallShift hE₀
    (perimeter_pos_of_volume hV hm₀.1.1 hm₀.2.1)
  let E₁ := (fun z ↦ z + quotientMap a) ⁻¹' E₀
  have hE₁ : MeasurableSet E₁ := hE₀.preimage (continuous_id.add continuous_const).measurable
  have hm₁ : IsMinimizerAt V E₁ := isMinimizerAt_translation hm₀ _
  obtain ⟨μ, hμ⟩ := exists_normalMeasure hE₁ hm₁.1.2.ne
  obtain ⟨H, hH⟩ := isMinimizerAt_exists_coordinate_multiplier hm₁ hE₁ hμ D hD.ne'
  have he : E₁ = (fun z ↦ z + quotientMap (b₀ + a)) ⁻¹' E := by
    ext z
    simp only [E₁, E₀, mem_preimage, quotientMap_add, add_assoc]
    rw [add_comm (quotientMap a) (quotientMap b₀)]
  refine ⟨b₀ + a, quarterCenter + a, μ, H, ?_, smallShift_center_ball ha, ?_, ?_⟩
  · have hec : quarterCenter + a + (b₀ + a) = shortestLift c + (a + a) := by
      dsimp [b₀]
      abel
    rw [hec, quotientMap_add, quotientMap_shortestLift, smallShift_double_quotient ha, add_zero]
  · rwa [he] at hμ
  · rwa [he] at hH

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

def halfspaceIndicator (n : Cover) (x : Cover) : ℝ :=
  {y | ⟪n, y⟫ < 0}.indicator (fun _ ↦ 1) x

lemma measurable_halfspaceIndicator (n : Cover) : Measurable (halfspaceIndicator n) :=
  measurable_const.indicator (isOpen_lt (innerSL ℝ n).continuous continuous_const).measurableSet

lemma halfspaceIndicator_bound (n x : Cover) : |halfspaceIndicator n x| ≤ 1 := by
  classical
  by_cases hx : ⟪n, x⟫ < 0 <;> simp [halfspaceIndicator, hx]

lemma hyperplane_volume_zero {n : Cover} (hn : ‖n‖ = 1) :
    volume {x : Cover | ⟪n, x⟫ = 0} = 0 := by
  apply Measure.addHaar_submodule volume (LinearMap.ker (innerSL ℝ n).toLinearMap)
  intro htop
  have hm : n ∈ LinearMap.ker (innerSL ℝ n).toLinearMap := by rw [htop]; trivial
  change ⟪n, n⟫ = 0 at hm
  rw [real_inner_self_eq_norm_sq, hn] at hm
  norm_num at hm

lemma HalfspaceTrappedAt.eventually_characteristic {U : Set Torus} {c : Torus} {n x : Cover}
    (htrap : HalfspaceTrappedAt U c n) (hx : ‖x‖ < 1) (hnx : ⟪n, x⟫ ≠ 0) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      characteristic U (quotientMap (r • x) + c) = halfspaceIndicator n x := by
  have hε : 0 < |⟪n, x⟫| / 2 := by positivity
  filter_upwards [htrap (|⟪n, x⟫| / 2) hε, self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))]
    with r hr hrpos hrsmall
  have hr0 : 0 < r := hrpos
  have hr4 : r < 1 / 4 := hrsmall
  have hnorm : ‖r • x‖ < r := by
    rw [norm_smul, Real.norm_of_nonneg hr0.le]
    nlinarith
  have hsl : shortestLift ((quotientMap (r • x) + c) - c) = r • x := by
    rw [add_sub_cancel_right]
    exact shortestLift_quotientMap (by linarith)
  have hd : dist (quotientMap (r • x) + c) c < r := by
    rw [dist_eq_norm, ← norm_shortestLift, hsl]
    exact hnorm
  by_cases hneg : ⟪n, x⟫ < 0
  · have hm : quotientMap (r • x) + c ∈ U := by
      apply hr.2
      refine ⟨hd, ?_⟩
      rw [hsl, inner_neg_left, inner_smul_right, abs_of_neg hneg]
      nlinarith [mul_neg_of_pos_of_neg hr0 hneg]
    simp [characteristic, halfspaceIndicator, hm, hneg]
  · have hpos : 0 < ⟪n, x⟫ := lt_of_le_of_ne (le_of_not_gt hneg) hnx.symm
    have hm : quotientMap (r • x) + c ∉ U := by
      have hh : quotientMap (r • x) + c ∈ (closure U)ᶜ := by
        apply hr.1
        refine ⟨hd, ?_⟩
        rw [hsl, inner_smul_right, abs_of_pos hpos]
        nlinarith [mul_pos hr0 hpos]
      exact fun h ↦ hh (subset_closure h)
    simp [characteristic, halfspaceIndicator, hm, hneg]

theorem HalfspaceTrappedAt.tendsto_integral_deviation {U : Set Torus} (hU : MeasurableSet U)
    {c : Torus} {n : Cover} (hn : ‖n‖ = 1) (htrap : HalfspaceTrappedAt U c n) :
    Tendsto (fun r : ℝ ↦ ∫ x in Metric.ball (0 : Cover) 1,
      |characteristic U (quotientMap (r • x) + c) - halfspaceIndicator n x|)
      (𝓝[>] 0) (𝓝 0) := by
  let ν : Measure Cover := volume.restrict (Metric.ball 0 1)
  have : IsFiniteMeasure ν := ⟨by
    rw [show ν = volume.restrict (Metric.ball (0 : Cover) 1) from rfl,
      Measure.restrict_apply_univ]
    exact (Metric.isBounded_ball (x := (0 : Cover)) (r := 1)).measure_lt_top⟩
  have hmeas (r : ℝ) : AEStronglyMeasurable
      (fun x : Cover ↦ |characteristic U (quotientMap (r • x) + c) - halfspaceIndicator n x|) ν := by
    have hs : Continuous (fun x : Cover ↦ r • x) := continuous_id.const_smul r
    have hc : Continuous (fun x : Cover ↦ quotientMap (r • x) + c) :=
      (continuous_quotientMap.comp hs).add continuous_const
    exact (((measurable_characteristic hU).comp hc.measurable).sub
      (measurable_halfspaceIndicator n)).abs.aestronglyMeasurable
  have hbound (r : ℝ) : ∀ᵐ x ∂ν,
      ‖|characteristic U (quotientMap (r • x) + c) - halfspaceIndicator n x|‖ ≤ (2 : ℝ) := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_abs]
    have ha := characteristic_bound U (quotientMap (r • x) + c)
    have hb := halfspaceIndicator_bound n x
    exact (abs_sub _ _).trans (by linarith)
  have hlim : ∀ᵐ x ∂ν, Tendsto
      (fun r : ℝ ↦ |characteristic U (quotientMap (r • x) + c) - halfspaceIndicator n x|)
      (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    have hne : ∀ᵐ x ∂(volume : Measure Cover), ⟪n, x⟫ ≠ 0 := by
      simpa only [ae_iff, not_not] using hyperplane_volume_zero hn
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet, ae_restrict_of_ae hne] with x hx hnx
    have hx' : ‖x‖ < 1 := by simpa using hx
    apply tendsto_const_nhds.congr'
    filter_upwards [htrap.eventually_characteristic hx' hnx] with r hr
    simp only [hr, sub_self, abs_zero]
  simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence (fun _ : Cover ↦ (2 : ℝ))
    (Eventually.of_forall hmeas) (Eventually.of_forall hbound) (integrable_const _) hlim

theorem isMinimizerAt_halfspace_blowup_ae {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) :
    ∀ᵐ c ∂(spatialNormalMeasure μ : Measure Torus),
      Tendsto (fun r : ℝ ↦ ∫ x in Metric.ball (0 : Cover) 1,
        |characteristic (openRepresentative E) (quotientMap (r • x) + c) - halfspaceIndicator (N c) x|)
        (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [isMinimizerAt_halfspace_trapped_ae hV hE hmin hμ hN hpolar hn, hn]
    with c hc hnc
  exact hc.tendsto_integral_deviation (isOpen_openRepresentative E).measurableSet hnc

end CubicTorus

end
end

end

end OAI
