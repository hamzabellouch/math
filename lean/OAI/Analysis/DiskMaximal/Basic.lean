import OAI.Analysis.DiskMaximal.Model

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

namespace CenteredDiskEndpoint

/-- The normalization is precisely planar Lebesgue disk area. -/
theorem volume_disk (x : Plane) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.ball x r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [EuclideanSpace.volume_ball_fin_two, ENNReal.ofReal_mul Real.pi_nonneg,
    ENNReal.ofReal_pow hr]
  exact mul_comm _ _

/-- For every admissible input and positive radius the extended average agrees
with the real absolute-value average, rather than a signed average. -/
theorem absoluteDiskAverage_eq_ofReal {f : Plane → ℝ} {x : Plane} {r : ℝ}
    (hf : IntegrableOn f (Metric.ball x r)) (hr : 0 < r) :
    absoluteDiskAverage f x r = ENNReal.ofReal (diskAverage (fun y => |f y|) x r) := by
  have hden : 0 < Real.pi * r ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hr)
  rw [absoluteDiskAverage, diskAverage, ENNReal.ofReal_div_of_pos hden,
    ofReal_integral_eq_lintegral_ofReal hf.abs (Filter.Eventually.of_forall (fun y => abs_nonneg (f y)))]

theorem absoluteDiskAverage_ne_top {f : Plane → ℝ} {x : Plane} {r : ℝ}
    (hf : IntegrableOn f (Metric.ball x r)) (hr : 0 < r) :
    absoluteDiskAverage f x r ≠ ⊤ := by
  rw [absoluteDiskAverage_eq_ofReal hf hr]
  exact ENNReal.ofReal_ne_top

theorem absoluteDiskAverage_le_maximal (f : Plane → ℝ) (x : Plane) {r : ℝ}
    (hr : 0 < r) : absoluteDiskAverage f x r ≤ maximal f x := by
  exact le_iSup_of_le r (le_iSup_of_le hr le_rfl)

theorem maximal_abs (f : Plane → ℝ) : maximal (fun y => |f y|) = maximal f := by
  funext x
  simp only [maximal, absoluteDiskAverage, abs_abs]

theorem inW11_of_gradient {f : Plane → ℝ} {g : Plane → Plane}
    (hf : Integrable f) (hg : Integrable g) (hw : HasWeakGradient f g) : InW11 f :=
  ⟨hf, g, hg, hw⟩

theorem inW11Loc_of_gradient {f : Plane → ℝ} {g : Plane → Plane}
    (hf : LocallyIntegrable f) (hg : Integrable g) (hw : HasWeakGradient f g) : InW11Loc f :=
  ⟨hf, g, hg.locallyIntegrable, hw⟩

theorem integral_smul_sub_const {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} {b : α → E} {K : α → ℝ}
    (hb : Integrable b μ) (hK : Integrable (fun y => K y • b y) μ)
    (hzero : ∫ y, b y ∂μ = 0) (c : ℝ) :
    (∫ y, (K y - c) • b y ∂μ) = ∫ y, K y • b y ∂μ := by
  simp_rw [sub_smul]
  have hc : Integrable (fun y => c • b y) μ := hb.smul c
  rw [integral_sub hK hc, integral_smul, hzero, smul_zero, sub_zero]

/-- The small-support zero-mass discount for actual integrable vector densities.
The kernel need only be Lipschitz; no smoothness or unproved moment estimate is
assumed. -/
theorem localized_cancellation {b : Plane → Plane} {K : Plane → ℝ}
    (hb : Integrable b) (hzero : ∫ y, b y = 0)
    {L : ℝ≥0} (hK : LipschitzWith L K) (z : Plane) {s : ℝ}
    (hsupp : ∀ᵐ y, b y ≠ 0 → ‖y - z‖ ≤ s) :
    ‖∫ y, K y • b y‖ ≤ (L : ℝ) * s * ∫ y, ‖b y‖ := by
  have hbound : ∀ᵐ y, ‖(K y - K z) • b y‖ ≤ ((L : ℝ) * s) * ‖b y‖ := by
    filter_upwards [hsupp] with y hy
    by_cases hby : b y = 0
    · simp [hby]
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_right
        ((hK.norm_sub_le y z).trans (mul_le_mul_of_nonneg_left (hy hby) L.coe_nonneg))
        (norm_nonneg _)
  have hdiff : Integrable (fun y => (K y - K z) • b y) :=
    (hb.norm.smul ((L : ℝ) * s)).mono'
      ((hK.continuous.sub continuous_const).aestronglyMeasurable.smul hb.aestronglyMeasurable)
      hbound
  have hprod : Integrable (fun y => K y • b y) := by
    have h := hdiff.add (hb.smul (K z))
    change Integrable (fun y => (K y - K z) • b y + K z • b y) at h
    simpa only [← add_smul, sub_add_cancel] using h
  rw [← integral_smul_sub_const hb hprod hzero (K z)]
  calc
    ‖∫ y, (K y - K z) • b y‖ ≤ ∫ y, ((L : ℝ) * s) * ‖b y‖ :=
      norm_integral_le_of_norm_le (hb.norm.smul ((L : ℝ) * s)) hbound
    _ = (L : ℝ) * s * ∫ y, ‖b y‖ := integral_const_mul _ _

end CenteredDiskEndpoint

namespace CenteredDiskEndpoint
open InnerProductSpace
open scoped RealInnerProductSpace

/-- A change of representatives on null sets does not change weak derivatives. -/
theorem HasWeakGradient.congr_ae {f f' : Plane → ℝ} {g g' : Plane → Plane}
    (h : HasWeakGradient f g) (hf : f =ᵐ[volume] f') (hg : g =ᵐ[volume] g') :
    HasWeakGradient f' g' := by
  intro φ hφ hφc i
  calc
    (∫ x, f' x * testPartial φ i x) = ∫ x, f x * testPartial φ i x := by
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      rw [hx]
    _ = -∫ x, g x i * φ x := h φ hφ hφc i
    _ = -∫ x, g' x i * φ x := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx]

theorem HasWeakGradient.ae_unique {f : Plane → ℝ} {g g' : Plane → Plane}
    (h : HasWeakGradient f g) (h' : HasWeakGradient f g')
    (hg : LocallyIntegrable g) (hg' : LocallyIntegrable g') : g =ᵐ[volume] g' := by
  have hcoord (i : Fin 2) : ∀ᵐ x, g x i = g' x i := by
    have hgi : LocallyIntegrable (fun x => g x i) := fun x =>
      (EuclideanSpace.proj (𝕜 := ℝ) i).integrableAtFilter_comp (hg x)
    have hgi' : LocallyIntegrable (fun x => g' x i) := fun x =>
      (EuclideanSpace.proj (𝕜 := ℝ) i).integrableAtFilter_comp (hg' x)
    apply ae_eq_of_integral_contDiff_smul_eq hgi hgi'
    intro φ hφ hφc
    have heq := (h φ hφ hφc i).symm.trans (h' φ hφ hφc i)
    simpa only [neg_inj, smul_eq_mul, mul_comm] using heq
  filter_upwards [ae_all_iff.mpr hcoord] with x hx
  ext i
  exact hx i

/-- Coordinate convention agreement with Mathlib's classical Euclidean gradient. -/
theorem classicalGradient_apply (f : Plane → ℝ) (x : Plane) (i : Fin 2) :
    gradient f x i = testPartial f i x := by
  simpa only [EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul, testPartial] using
    (inner_gradient_left (f := f) (x := x) (y := EuclideanSpace.single i 1))

/-- No integrability hypothesis is smuggled into the definition of the weak
identity: every C¹ function satisfies it when tested against compact support. -/
theorem contDiff_hasWeakGradient {f : Plane → ℝ} (hf : ContDiff ℝ 1 f) :
    HasWeakGradient f (gradient f) := by
  intro φ hφ hφc i
  have hfd : Continuous (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hφd : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφds : HasCompactSupport (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    hφc.fderiv_apply ℝ (EuclideanSpace.single i 1)
  simp_rw [classicalGradient_apply, testPartial]
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (hfd.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
  · exact (hf.continuous.mul hφd).integrable_of_hasCompactSupport hφds.mul_left
  · exact (hf.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
  · intro x _
    exact hf.differentiable one_ne_zero x
  · intro x _
    exact hφ.differentiable (by simp) x

end CenteredDiskEndpoint

open scoped RealInnerProductSpace

namespace CenteredDiskEndpoint
open Filter

/-- Spherical boundaries are null, so the choice of an open disk does not alter
Lebesgue differentiation averages. -/
theorem disk_ae_eq_closedDisk (x : Plane) (r : ℝ) :
    Metric.ball x r =ᵐ[volume] Metric.closedBall x r := by
  apply ae_eq_of_subset_of_measure_ge Metric.ball_subset_closedBall
  · exact (Measure.addHaar_closedBall_eq_addHaar_ball volume x r).le
  · exact measurableSet_ball.nullMeasurableSet
  · exact measure_closedBall_lt_top.ne

theorem average_closedDisk_eq (f : Plane → ℝ) (x : Plane) {r : ℝ} (hr : 0 ≤ r) :
    (⨍ y in Metric.closedBall x r, f y) = diskAverage f x r := by
  rw [← setAverage_congr (disk_ae_eq_closedDisk x r), setAverage_eq,
    diskAverage, measureReal_def, volume_disk x hr, ENNReal.toReal_ofReal (by positivity)]
  simp only [smul_eq_mul, div_eq_inv_mul]

/-- Almost every point is a Lebesgue point for absolute disk averages. -/
theorem ae_tendsto_diskAverage_abs {f : Plane → ℝ} (hf : Integrable f) :
    ∀ᵐ x, Tendsto (fun r => diskAverage (fun y => |f y|) x r)
      (𝓝[>] (0 : ℝ)) (𝓝 |f x|) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average volume hf.abs.locallyIntegrable 0]
    with x hx
  have h := hx (fun _ : ℝ => x) (fun r : ℝ => r) tendsto_id
    (Eventually.of_forall (fun r => by simp))
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact average_closedDisk_eq (fun y => |f y|) x hr.le

/-- Away from zero the denominator alone bounds all absolute averages. -/
theorem diskAverage_abs_le_of_radius_le {f : Plane → ℝ} (hf : Integrable f)
    (x : Plane) {a r : ℝ} (ha : 0 < a) (har : a ≤ r) :
    diskAverage (fun y => |f y|) x r ≤ (∫ y, |f y|) / (Real.pi * a ^ 2) := by
  have hr : 0 < r := ha.trans_le har
  have hnum : (∫ y in Metric.ball x r, |f y|) ≤ ∫ y, |f y| :=
    integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall (fun y => abs_nonneg (f y))) hf.abs
  have hden : Real.pi * a ^ 2 ≤ Real.pi * r ^ 2 :=
    mul_le_mul_of_nonneg_left ((sq_le_sq₀ ha.le hr.le).2 har) Real.pi_nonneg
  dsimp [diskAverage]
  calc
    (∫ y in Metric.ball x r, |f y|) / (Real.pi * r ^ 2) ≤
        (∫ y, |f y|) / (Real.pi * r ^ 2) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (∫ y, |f y|) / (Real.pi * a ^ 2) :=
      div_le_div_of_nonneg_left (integral_nonneg (fun y => abs_nonneg (f y)))
        (by positivity) hden

/-- A genuine clause of the endpoint, in fact valid for every L¹ input. No
maximal bound, gradient hypothesis, or selected radius is used here. -/
theorem ae_maximal_ne_top {f : Plane → ℝ} (hf : Integrable f) :
    ∀ᵐ x, maximal f x ≠ ⊤ := by
  filter_upwards [ae_tendsto_diskAverage_abs hf] with x hx
  obtain ⟨C, hC⟩ := hx.isBoundedUnder_le
  obtain ⟨a, ha, haC⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hC
  have hbound (r : ℝ) (hr : 0 < r) :
      diskAverage (fun y => |f y|) x r ≤ max C ((∫ y, |f y|) / (Real.pi * a ^ 2)) := by
    by_cases hra : r ≤ a
    · exact (haC ⟨hr, hra⟩).trans (le_max_left _ _)
    · exact (diskAverage_abs_le_of_radius_le hf x ha (le_of_not_ge hra)).trans
        (le_max_right _ _)
  have hmax : maximal f x ≤ ENNReal.ofReal
      (max C ((∫ y, |f y|) / (Real.pi * a ^ 2))) := by
    apply iSup_le
    intro r
    apply iSup_le
    intro hr
    rw [absoluteDiskAverage_eq_ofReal hf.integrableOn hr]
    exact ENNReal.ofReal_le_ofReal (hbound r hr)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmax

end CenteredDiskEndpoint

open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section

open scoped Real RealInnerProductSpace

end
end

end OAI
