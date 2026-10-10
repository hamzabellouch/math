import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Estimates.ConeJacobianMatrix2
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereChartScale2

namespace OAI

/-! Fourier kernels and oscillatory estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open MeasureTheory Set Metric Module
open scoped RealInnerProductSpace Topology ENNReal Pointwise
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma sphereConeND_toLp (p : V × ℝ) :
    WithLp.toLp 2 (sphereConeND p) = p.2 • sphereChartND p.1 := rfl

lemma sphereConeND_norm {p : V × ℝ} (hp : ‖p.1‖ ≤ 2) :
    ‖WithLp.toLp 2 (sphereConeND p)‖ = |p.2| := by
  rw [sphereConeND_toLp, norm_smul, sphereChartND_norm hp, mul_one, Real.norm_eq_abs]

lemma sphereConeND_injOn : InjOn (sphereConeND : V × ℝ → V × ℝ)
    (ball 0 2 ×ˢ Ioi 0) := by
  intro p hp q hq he
  have hp' : ‖p.1‖ < 2 := by simpa using hp.1
  have hq' : ‖q.1‖ < 2 := by simpa using hq.1
  have hn := congrArg (fun z : V × ℝ => ‖WithLp.toLp 2 z‖) he
  rw [sphereConeND_norm hp'.le, sphereConeND_norm hq'.le,
    abs_of_pos hp.2, abs_of_pos hq.2] at hn
  have hc := congrArg (WithLp.toLp 2) he
  rw [sphereConeND_toLp, sphereConeND_toLp, hn] at hc
  have hu := smul_right_injective (WithLp 2 (V × ℝ)) (show q.2 ≠ 0 from ne_of_gt hq.2) hc
  exact Prod.ext (sphereChartND_injOn hp.1 hq.1 hu) hn

section Matrix
variable {n : ℕ}

noncomputable def coneBasisND (n : ℕ) :
    Basis (Fin n ⊕ Unit) ℝ (EuclideanSpace ℝ (Fin n) × ℝ) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.prod (Basis.singleton Unit ℝ)

lemma sphereConeDerivND_toMatrix (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    LinearMap.toMatrix (coneBasisND n) (coneBasisND n)
      (sphereConeDerivND p).toLinearMap = coneJacobianMatrix p.1 p.2 (sphereChartScaleND p.1) := by
  classical
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp [LinearMap.toMatrix_apply, coneBasisND, sphereConeDerivND_apply,
        coneJacobianMatrix, EuclideanSpace.basisFun_apply, Matrix.mul_apply,
        PiLp.single_apply, EuclideanSpace.inner_single_right, Matrix.one_apply]
      split_ifs <;> ring
    | inr j =>
      simp [LinearMap.toMatrix_apply, coneBasisND, sphereConeDerivND_apply,
        coneJacobianMatrix]
  | inr i =>
    cases j with
    | inl j =>
      simp [LinearMap.toMatrix_apply, coneBasisND, sphereConeDerivND_apply,
        coneJacobianMatrix, EuclideanSpace.inner_single_right]
    | inr j =>
      simp [LinearMap.toMatrix_apply, coneBasisND, sphereConeDerivND_apply,
        coneJacobianMatrix, EuclideanSpace.real_norm_sq_eq]

lemma sphereConeDerivND_det {p : EuclideanSpace ℝ (Fin n) × ℝ}
    (hu : ‖p.1‖ < 2) (hr : p.2 ≠ 0) :
    (sphereConeDerivND p).det = (p.2*sphereChartScaleND p.1)^n / (sphereChartScaleND p.1)^2 := by
  change LinearMap.det (sphereConeDerivND p).toLinearMap = _
  rw [← LinearMap.det_toMatrix (coneBasisND n), sphereConeDerivND_toMatrix]
  have hsq : (sphereChartScaleND p.1)^2 = 1-(∑ i, (p.1 i)^2)/4 := by
    rw [sphereChartScaleND_sq hu.le]
    congr 2
    exact EuclideanSpace.real_norm_sq_eq p.1
  simpa using coneJacobianMatrix_det (fun i => p.1 i) hr (sphereChartScaleND_pos hu).ne' hsq

lemma lintegral_unitInterval_powND (n : ℕ) :
    (∫⁻ r in Ioo (0:ℝ) 1, ENNReal.ofReal (r^n)) = ((n:ℝ≥0∞)+1)⁻¹ := by
  have hi : IntegrableOn (fun r : ℝ => r^n) (Ioo 0 1) :=
    (continuous_id.pow n).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hn : 0 ≤ᵐ[volume.restrict (Ioo (0:ℝ) 1)] (fun r => r^n) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact pow_nonneg hr.1.le _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num), integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero, one_div]
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_add (by positivity) zero_le_one]
  simp

noncomputable def sphereChartWeightND (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sphereChartScaleND u ^ n / sphereChartScaleND u ^ 2

lemma sphereChartWeightND_measurable :
    Measurable (sphereChartWeightND : EuclideanSpace ℝ (Fin n) → ℝ) := by
  unfold sphereChartWeightND sphereChartScaleND
  fun_prop

lemma sphereChartWeightND_pos {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    0 < sphereChartWeightND u := by
  unfold sphereChartWeightND
  exact div_pos (pow_pos (sphereChartScaleND_pos hu) _) (sq_pos_of_pos (sphereChartScaleND_pos hu))

lemma sphereConeND_volume {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s)
    (hsb : s ⊆ ball 0 2) :
    volume (sphereConeND '' (s ×ˢ Ioo (0:ℝ) 1)) =
      (∫⁻ u in s, ENNReal.ofReal (sphereChartWeightND u)) * ((n:ℝ≥0∞)+1)⁻¹ := by
  let : (volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hsub : s ×ˢ Ioo (0:ℝ) 1 ⊆ ball 0 2 ×ˢ Ioi (0:ℝ) :=
    prod_mono hsb Ioo_subset_Ioi_self
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image (volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)) (hs.prod measurableSet_Ioo)
    (f' := sphereConeDerivND)
    (fun p hp => (sphereConeND_hasStrictFDerivAt (by simpa using hsb hp.1)).hasFDerivAt.hasFDerivWithinAt)
    (sphereConeND_injOn.mono hsub)]
  have he : (fun p : EuclideanSpace ℝ (Fin n) × ℝ => ENNReal.ofReal |(sphereConeDerivND p).det|)
      =ᵐ[volume.restrict (s ×ˢ Ioo (0:ℝ) 1)]
      (fun p => ENNReal.ofReal (sphereChartWeightND p.1) * ENNReal.ofReal (p.2^n)) := by
    filter_upwards [ae_restrict_mem (hs.prod measurableSet_Ioo)] with p hp
    have hu : ‖p.1‖ < 2 := by simpa using hsb hp.1
    rw [sphereConeDerivND_det hu hp.2.1.ne']
    have hpos : 0 ≤ (p.2*sphereChartScaleND p.1)^n / sphereChartScaleND p.1 ^ 2 := by
      exact div_nonneg (pow_nonneg (mul_nonneg hp.2.1.le (sphereChartScaleND_pos hu).le) _)
        (sq_nonneg _)
    rw [abs_of_nonneg hpos]
    rw [← ENNReal.ofReal_mul (sphereChartWeightND_pos hu).le]
    congr 1
    dsimp [sphereChartWeightND]
    rw [mul_pow]
    ring
  rw [lintegral_congr_ae he, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hf : Measurable (fun u : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (sphereChartWeightND u)) :=
    sphereChartWeightND_measurable.ennreal_ofReal
  have hg : Measurable (fun r : ℝ => ENNReal.ofReal (r^n)) := by fun_prop
  rw [lintegral_prod_mul hf.aemeasurable hg.aemeasurable, lintegral_unitInterval_powND]

lemma sphereConeND_measurableSet_image {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : MeasurableSet s) (hsb : s ⊆ ball 0 2) :
    MeasurableSet (sphereConeND '' (s ×ˢ Ioo (0:ℝ) 1)) := by
  apply (hs.prod measurableSet_Ioo).image_of_continuousOn_injOn
  · intro p hp
    exact (sphereConeND_hasStrictFDerivAt
      (by simpa using hsb hp.1)).continuousAt.continuousWithinAt
  · exact sphereConeND_injOn.mono (prod_mono hsb Ioo_subset_Ioi_self)

lemma sphereConeND_preimage_image (s : Set (EuclideanSpace ℝ (Fin n))) :
    WithLp.ofLp ⁻¹' (sphereConeND '' (s ×ˢ Ioo (0:ℝ) 1)) =
      Ioo (0:ℝ) 1 • (sphereChartND '' s) := by
  ext w
  constructor
  · rintro ⟨⟨u,r⟩, ⟨hu,hr⟩,he⟩
    refine ⟨r,hr,sphereChartND u,⟨u,hu,rfl⟩,?_⟩
    exact congrArg (WithLp.toLp 2) he
  · rintro ⟨r,hr,_,⟨u,hu,rfl⟩,he⟩
    refine ⟨(u,r),⟨hu,hr⟩,?_⟩
    exact congrArg WithLp.ofLp he

lemma sphereChartND_surface_measure {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : MeasurableSet s) (hsb : s ⊆ ball 0 2) :
    (volume : Measure (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ))).toSphere
      {w | (w : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) ∈ sphereChartND '' s} =
      ∫⁻ u in s, ENNReal.ofReal (sphereChartWeightND u) := by
  have hm : MeasurableSet (sphereChartND '' s) := hs.image_of_continuousOn_injOn
    (sphereChartND_contDiffOn.continuousOn.mono hsb) (sphereChartND_injOn.mono hsb)
  have himage : (Subtype.val : sphere (0 : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) 1 → _) ''
      {w | (w : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) ∈ sphereChartND '' s} = sphereChartND '' s := by
    ext w
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact hv
    · intro hw
      have hsw : w ∈ sphere (0 : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) 1 := by
        rcases hw with ⟨u,hu,rfl⟩
        exact sphereChartND_mem_sphere (by exact le_of_lt (by simpa using hsb hu))
      exact ⟨⟨w,hsw⟩,hw,rfl⟩
  rw [Measure.toSphere_apply' (volume : Measure (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)))
    (show MeasurableSet {w : sphere (0 : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) 1 |
      (w : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) ∈ sphereChartND '' s} from
        hm.preimage measurable_subtype_coe), himage]
  have hv := (WithLp.volume_preserving_ofLp (EuclideanSpace ℝ (Fin n)) ℝ).measure_preimage
    (sphereConeND_measurableSet_image hs hsb).nullMeasurableSet
  rw [sphereConeND_preimage_image] at hv
  rw [hv, sphereConeND_volume hs hsb]
  have hd : Module.finrank ℝ (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) = n+1 := by
    rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq, Module.finrank_prod]
    simp
  rw [hd, Nat.cast_add, Nat.cast_one]
  rw [mul_comm _ ((∫⁻ u in s, ENNReal.ofReal (sphereChartWeightND u)) * _), mul_assoc,
    ENNReal.inv_mul_cancel (by positivity) (by finiteness), mul_one]

lemma sphereChartND_continuous :
    Continuous (sphereChartND : EuclideanSpace ℝ (Fin n) → _) := by
  unfold sphereChartND sphereChartScaleND
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin n)) ℝ).symm.continuous.comp
    (by fun_prop)

noncomputable def sphereAreaND (n : ℕ) : Measure (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) :=
  Measure.map Subtype.val (volume : Measure (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ))).toSphere

lemma sphereAreaND_chart {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : MeasurableSet s) (hsb : s ⊆ ball 0 2) :
    sphereAreaND n (sphereChartND '' s) = ∫⁻ u in s, ENNReal.ofReal (sphereChartWeightND u) := by
  rw [sphereAreaND, Measure.map_apply measurable_subtype_coe
    (hs.image_of_continuousOn_injOn sphereChartND_continuous.continuousOn (sphereChartND_injOn.mono hsb))]
  exact sphereChartND_surface_measure hs hsb

lemma sphereAreaND_restrict_chart {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : MeasurableSet s) (hsb : s ⊆ ball 0 2) :
    (sphereAreaND n).restrict (sphereChartND '' s) =
      Measure.map sphereChartND ((volume.restrict s).withDensity (fun u => ENNReal.ofReal (sphereChartWeightND u))) := by
  ext t ht
  rw [Measure.restrict_apply ht, Measure.map_apply sphereChartND_continuous.measurable ht,
    withDensity_apply _ (sphereChartND_continuous.measurable ht),
    Measure.restrict_restrict (sphereChartND_continuous.measurable ht)]
  have hset : t ∩ sphereChartND '' s = sphereChartND '' (sphereChartND ⁻¹' t ∩ s) := by
    ext w
    simp only [mem_inter_iff, mem_image, mem_preimage]
    constructor
    · rintro ⟨hw, u, hu, rfl⟩
      exact ⟨u,⟨hw,hu⟩,rfl⟩
    · rintro ⟨u,⟨hu,hsu⟩,rfl⟩
      exact ⟨hu,u,hsu,rfl⟩
  rw [hset, sphereAreaND_chart ((sphereChartND_continuous.measurable ht).inter hs)
    (inter_subset_right.trans hsb)]

lemma integral_sphereAreaND_chart {F : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) → ℂ}
    (hF : StronglyMeasurable F) {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : MeasurableSet s) (hsb : s ⊆ ball 0 2) :
    (∫ w in sphereChartND '' s, F w ∂sphereAreaND n) =
      ∫ u in s, (sphereChartWeightND u : ℂ) * F (sphereChartND u) := by
  rw [sphereAreaND_restrict_chart hs hsb,
    integral_map_of_stronglyMeasurable sphereChartND_continuous.measurable hF,
    integral_withDensity_eq_integral_toReal_smul
      sphereChartWeightND_measurable.ennreal_ofReal (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hs] with u hu
  rw [ENNReal.toReal_ofReal (sphereChartWeightND_pos (by simpa using hsb hu)).le]
  rfl

lemma sphereChartWeightND_eq_source {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    sphereChartWeightND u = (1-‖u‖^2/4) ^ (((n:ℝ)-2)/2) := by
  have hp : 0 < 1-‖u‖^2/4 := by nlinarith [norm_nonneg u]
  rw [sphereChartWeightND, ← Real.rpow_natCast (sphereChartScaleND u) n,
    ← Real.rpow_natCast (sphereChartScaleND u) 2, sphereChartScaleND, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hp.le, ← Real.rpow_mul hp.le,
    ← Real.rpow_sub hp]
  congr 1
  ring

lemma sphereChartND_exponential (Λ : ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    Complex.exp (Complex.I * Λ * (inner ℝ (sphereChartND u) (WithLp.toLp 2 (0,(1:ℝ))) : ℂ)) =
      Complex.exp (Complex.I * Λ) * Complex.exp (-((Λ/2:ℝ) : ℂ)*Complex.I*(‖u‖:ℂ)^2) := by
  rw [sphereChartND_phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma integral_sphereAreaND_quadratic {b : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) → ℂ}
    (hb : StronglyMeasurable b) {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : MeasurableSet s) (hsb : s ⊆ ball 0 2) (Λ : ℝ) :
    (∫ w in sphereChartND '' s, Complex.exp (Complex.I * Λ *
      (inner ℝ w (WithLp.toLp 2 (0,(1:ℝ))) : ℂ)) * b w ∂sphereAreaND n) =
      Complex.exp (Complex.I * Λ) * ∫ u in s,
        Complex.exp (-((Λ/2:ℝ) : ℂ)*Complex.I*(‖u‖:ℂ)^2) *
          ((sphereChartWeightND u : ℂ) * b (sphereChartND u)) := by
  rw [integral_sphereAreaND_chart (by fun_prop) hs hsb, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [sphereChartND_exponential]
  ring

open scoped ContDiff SchwartzMap

noncomputable def sphereChartAmplitudeND
    (b : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) → ℂ)
    (u : EuclideanSpace ℝ (Fin n)) : ℂ :=
  (sphereChartWeightND u : ℂ) * b (sphereChartND u)

lemma sphereChartWeightND_zero {u : EuclideanSpace ℝ (Fin n)} (hu : 2 ≤ ‖u‖) :
    sphereChartWeightND u = 0 := by
  have h : 1-‖u‖^2/4 ≤ 0 := by nlinarith [norm_nonneg u]
  simp [sphereChartWeightND, sphereChartScaleND, Real.sqrt_eq_zero_of_nonpos h]

lemma sphereChartWeightND_contDiffOn :
    ContDiffOn ℝ ∞ (sphereChartWeightND : EuclideanSpace ℝ (Fin n) → ℝ) (ball 0 2) := by
  apply ((sphereChartScaleND_contDiffOn.of_le le_top).pow n).div
    ((sphereChartScaleND_contDiffOn.of_le le_top).pow 2)
  intro u hu
  exact pow_ne_zero _ (sphereChartScaleND_pos (by simpa using hu)).ne'

lemma sphereChartAmplitudeND_zero
    {b : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) → ℂ} {r : ℝ}
    (hr : 0 ≤ r)
    (hb : ∀ w, ‖w‖ = 1 → (WithLp.ofLp w).2 ≤ 1-r^2/2 → b w = 0)
    {u : EuclideanSpace ℝ (Fin n)} (hu : r ≤ ‖u‖) :
    sphereChartAmplitudeND b u = 0 := by
  by_cases hu2 : 2 ≤ ‖u‖
  · simp [sphereChartAmplitudeND, sphereChartWeightND_zero hu2]
  · have hu2' : ‖u‖ < 2 := lt_of_not_ge hu2
    have hb0 := hb (sphereChartND u) (sphereChartND_norm hu2'.le)
      (show 1-‖u‖^2/2 ≤ 1-r^2/2 by nlinarith)
    simp [sphereChartAmplitudeND, hb0]

lemma sphereChartAmplitudeND_tsupport
    {b : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) → ℂ} {r : ℝ}
    (hr : 0 ≤ r)
    (hb : ∀ w, ‖w‖ = 1 → (WithLp.ofLp w).2 ≤ 1-r^2/2 → b w = 0) :
    tsupport (sphereChartAmplitudeND b) ⊆ closedBall 0 r := by
  apply closure_minimal _ isClosed_closedBall
  apply Function.support_subset_iff'.mpr
  intro u hu
  exact sphereChartAmplitudeND_zero hr hb (le_of_lt (by simpa using hu))

lemma sphereChartAmplitudeND_hasCompactSupport
    {b : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) → ℂ} {r : ℝ}
    (hr : 0 ≤ r)
    (hb : ∀ w, ‖w‖ = 1 → (WithLp.ofLp w).2 ≤ 1-r^2/2 → b w = 0) :
    HasCompactSupport (sphereChartAmplitudeND b) :=
  (isCompact_closedBall 0 r).of_isClosed_subset (isClosed_tsupport _)
    (sphereChartAmplitudeND_tsupport hr hb)

lemma sphereChartAmplitudeND_contDiff
    {b : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) → ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hr2 : r < 2) (hb : ContDiff ℝ ∞ b)
    (hsupp : ∀ w, ‖w‖ = 1 → (WithLp.ofLp w).2 ≤ 1-r^2/2 → b w = 0) :
    ContDiff ℝ ∞ (sphereChartAmplitudeND b) := by
  have hlocal : ContDiffOn ℝ ∞ (sphereChartAmplitudeND b) (ball 0 2) := by
    exact (Complex.ofRealCLM.contDiff.comp_contDiffOn sphereChartWeightND_contDiffOn).mul
      (hb.comp_contDiffOn (sphereChartND_contDiffOn.of_le le_top))
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : ‖u‖ < 2
  · exact hlocal.contDiffAt (isOpen_ball.mem_nhds (by simpa using hu))
  · have hur : r < ‖u‖ := hr2.trans_le (le_of_not_gt hu)
    have hv : ∀ᶠ v in 𝓝 u, r < ‖v‖ := (isOpen_lt continuous_const continuous_norm).mem_nhds hur
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hv] with v hv
    exact sphereChartAmplitudeND_zero hr hsupp hv.le

noncomputable def sphereChartSchwartzND
    (b : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) → ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hr2 : r < 2) (hb : ContDiff ℝ ∞ b)
    (hsupp : ∀ w, ‖w‖ = 1 → (WithLp.ofLp w).2 ≤ 1-r^2/2 → b w = 0) :
    𝓢(EuclideanSpace ℝ (Fin n),ℂ) :=
  (sphereChartAmplitudeND_hasCompactSupport hr hsupp).toSchwartzMap
    (sphereChartAmplitudeND_contDiff hr hr2 hb hsupp)

end Matrix
end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
