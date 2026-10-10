import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped Topology ENNReal
namespace Problem358

/-- A positive continuous density on an open bounded interval. Endpoint values are irrelevant. -/
structure PositiveIntervalDensity where
  lower : ℝ
  upper : ℝ
  density : ℝ → ℝ
  lower_lt_upper : lower < upper
  integrable : IntervalIntegrable density volume lower upper
  continuousOn : ContinuousOn density (Ioo lower upper)
  positive : ∀ x ∈ Ioo lower upper, 0 < density x
  integral_one : (∫ x in lower..upper, density x) = 1

namespace PositiveIntervalDensity

variable (D : PositiveIntervalDensity)

/-- The cumulative integral starting at the lower endpoint. -/
def cdf (x : ℝ) : ℝ := ∫ t in D.lower..x, D.density t

@[simp] lemma cdf_lower : D.cdf D.lower = 0 := by simp [cdf]
@[simp] lemma cdf_upper : D.cdf D.upper = 1 := D.integral_one

lemma cdf_continuousOn : ContinuousOn D.cdf (Icc D.lower D.upper) := by
  change ContinuousOn (fun x : ℝ => ∫ t in D.lower..x, D.density t) (Icc D.lower D.upper)
  simpa only [uIcc_of_le D.lower_lt_upper.le] using
    (intervalIntegral.continuousOn_primitive_interval' D.integrable left_mem_uIcc)

lemma cdf_hasDerivAt {x : ℝ} (hx : x ∈ Ioo D.lower D.upper) :
    HasDerivAt D.cdf (D.density x) x := by
  have hx' : x ∈ uIcc D.lower D.upper := by
    rw [uIcc_of_le D.lower_lt_upper.le]
    exact ⟨hx.1.le, hx.2.le⟩
  exact intervalIntegral.integral_hasDerivAt_right
    (D.integrable.mono_set (uIcc_subset_uIcc left_mem_uIcc hx'))
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo D.continuousOn x hx)
    (D.continuousOn.continuousAt (isOpen_Ioo.mem_nhds hx))

lemma cdf_strictMonoOn : StrictMonoOn D.cdf (Icc D.lower D.upper) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) D.cdf_continuousOn
  intro x hx
  have hx' : x ∈ Ioo D.lower D.upper := by simpa only [interior_Icc] using hx
  rw [(D.cdf_hasDerivAt hx').deriv]
  exact D.positive x hx'

lemma cdf_image : D.cdf '' Icc D.lower D.upper = Icc (0 : ℝ) 1 := by
  simpa only [D.cdf_lower, D.cdf_upper] using
    D.cdf_continuousOn.image_Icc_of_monotoneOn D.lower_lt_upper.le
      D.cdf_strictMonoOn.monotoneOn

lemma existsUnique_cdf_eq {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    ∃! x : ℝ, x ∈ Ioo D.lower D.upper ∧ D.cdf x = s := by
  have hs' : s ∈ D.cdf '' Icc D.lower D.upper := by
    rw [D.cdf_image]
    exact ⟨hs.1.le, hs.2.le⟩
  obtain ⟨x, hx, hxs⟩ := hs'
  have hx0 : D.lower < x := by
    apply lt_of_le_of_ne hx.1
    intro heq
    have hh : s = 0 := by rw [← hxs, ← heq, D.cdf_lower]
    linarith [hs.1]
  have hx1 : x < D.upper := by
    apply lt_of_le_of_ne hx.2
    intro heq
    have hh : s = 1 := by rw [← hxs, heq, D.cdf_upper]
    linarith [hs.2]
  refine ⟨x, ⟨⟨hx0, hx1⟩, hxs⟩, ?_⟩
  intro y hy
  exact D.cdf_strictMonoOn.injOn ⟨hy.1.1.le, hy.1.2.le⟩ hx (hy.2.trans hxs.symm)

/-- Cumulative integration is an order isomorphism between the two compact intervals. -/
def cdfOrderIso : Icc D.lower D.upper ≃o Icc (0 : ℝ) 1 :=
  (StrictMonoOn.orderIso D.cdf (Icc D.lower D.upper) D.cdf_strictMonoOn).trans
    (Set.orderIsoOfEq _ _ D.cdf_image)

/-- The inverse cumulative map, including its continuous endpoint extension. -/
def quantile (s : Icc (0 : ℝ) 1) : ℝ := (D.cdfOrderIso.symm s).1

lemma quantile_mem (s : Icc (0 : ℝ) 1) : D.quantile s ∈ Icc D.lower D.upper :=
  (D.cdfOrderIso.symm s).2

lemma quantile_continuous : Continuous D.quantile := by
  exact continuous_subtype_val.comp D.cdfOrderIso.symm.toHomeomorph.continuous

lemma cdf_quantile (s : Icc (0 : ℝ) 1) : D.cdf (D.quantile s) = s := by
  have h := congrArg Subtype.val (D.cdfOrderIso.apply_symm_apply s)
  exact h

lemma quantile_mem_interior {s : Icc (0 : ℝ) 1} (hs : (s : ℝ) ∈ Ioo (0 : ℝ) 1) :
    D.quantile s ∈ Ioo D.lower D.upper := by
  have hm := D.quantile_mem s
  have hc := D.cdf_quantile s
  constructor
  · apply lt_of_le_of_ne hm.1
    intro heq
    rw [← heq, D.cdf_lower] at hc
    linarith [hs.1]
  · apply lt_of_le_of_ne hm.2
    intro heq
    rw [heq, D.cdf_upper] at hc
    linarith [hs.2]

/-- A globally continuous extension of the quantile, constant outside the unit interval. -/
def quantileReal (s : ℝ) : ℝ := D.quantile (Set.projIcc 0 1 (by norm_num) s)

lemma quantileReal_continuous : Continuous D.quantileReal :=
  D.quantile_continuous.comp continuous_projIcc

lemma quantileReal_eq (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    D.quantileReal s = D.quantile ⟨s, hs⟩ := by
  rw [quantileReal, Set.projIcc_of_mem _ hs]

lemma cdf_quantileReal {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    D.cdf (D.quantileReal s) = s := by
  rw [D.quantileReal_eq s hs]
  exact D.cdf_quantile ⟨s, hs⟩

lemma quantileReal_mem_interior {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    D.quantileReal s ∈ Ioo D.lower D.upper := by
  rw [D.quantileReal_eq s ⟨hs.1.le, hs.2.le⟩]
  exact D.quantile_mem_interior hs

/-- The one-dimensional inverse-density derivative used in the triangular coupling. -/
lemma quantileReal_hasDerivAt {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt D.quantileReal (D.density (D.quantileReal s))⁻¹ s := by
  apply HasDerivAt.of_local_left_inverse D.quantileReal_continuous.continuousAt
    (D.cdf_hasDerivAt (D.quantileReal_mem_interior hs))
    (D.positive _ (D.quantileReal_mem_interior hs)).ne'
  filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
  exact D.cdf_quantileReal ⟨ht.1.le, ht.2.le⟩

lemma quantileReal_deriv_pos {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    0 < deriv D.quantileReal s := by
  rw [(D.quantileReal_hasDerivAt hs).deriv]
  exact inv_pos.mpr (D.positive _ (D.quantileReal_mem_interior hs))

lemma cdf_image_Ioo : D.cdf '' Ioo D.lower D.upper = Ioo (0 : ℝ) 1 := by
  simpa only [D.cdf_lower, D.cdf_upper] using
    D.cdf_continuousOn.image_Ioo_of_strictMonoOn D.lower_lt_upper.le D.cdf_strictMonoOn

lemma quantileReal_mem (s : ℝ) : D.quantileReal s ∈ Icc D.lower D.upper :=
  D.quantile_mem _

lemma quantileReal_cdf {x : ℝ} (hx : x ∈ Icc D.lower D.upper) :
    D.quantileReal (D.cdf x) = x := by
  have hc : D.cdf x ∈ Icc (0 : ℝ) 1 := by
    rw [← D.cdf_image]
    exact ⟨x, hx, rfl⟩
  apply D.cdf_strictMonoOn.injOn (D.quantileReal_mem _) hx
  exact D.cdf_quantileReal hc

/-- The probability distribution with the given density, restricted to its open interval. -/
def densityMeasure : Measure ℝ :=
  (volume.restrict (Ioo D.lower D.upper)).withDensity (fun x => ENNReal.ofReal (D.density x))

lemma densityMeasure_ae_mem : ∀ᵐ x ∂D.densityMeasure, x ∈ Ioo D.lower D.upper :=
  (ae_restrict_mem measurableSet_Ioo).filter_mono
    (withDensity_absolutelyContinuous _ _).ae_le

lemma cdf_aemeasurable : AEMeasurable D.cdf D.densityMeasure := by
  apply AEMeasurable.mono_ac _ (withDensity_absolutelyContinuous _ _)
  exact (D.cdf_continuousOn.mono Ioo_subset_Icc_self).aemeasurable measurableSet_Ioo

/-- The change-of-variables theorem sends the positive density to the unit uniform law. -/
lemma map_cdf_densityMeasure :
    Measure.map D.cdf D.densityMeasure = volume.restrict (Ioo (0 : ℝ) 1) := by
  have hmap := map_withDensity_abs_det_fderiv_eq_addHaar volume
    measurableSet_Ioo.nullMeasurableSet
    (fun x hx => (D.cdf_hasDerivAt hx).hasDerivWithinAt.hasFDerivWithinAt)
    (D.cdf_strictMonoOn.injOn.mono Ioo_subset_Icc_self)
  simp only [ContinuousLinearMap.det_toSpanSingleton] at hmap
  have hden : (volume.restrict (Ioo D.lower D.upper)).withDensity
      (fun x => ENNReal.ofReal |D.density x|) = D.densityMeasure := by
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [abs_of_pos (D.positive x hx)]
  rw [hden, D.cdf_image_Ioo] at hmap
  exact hmap

/-- The quantile constructed above really has the prescribed density law. -/
lemma map_quantileReal_uniform :
    Measure.map D.quantileReal (volume.restrict (Ioo (0 : ℝ) 1)) = D.densityMeasure := by
  rw [← D.map_cdf_densityMeasure,
    AEMeasurable.map_map_of_aemeasurable D.quantileReal_continuous.measurable.aemeasurable
      D.cdf_aemeasurable]
  calc
    Measure.map (D.quantileReal ∘ D.cdf) D.densityMeasure = Measure.map id D.densityMeasure := by
      apply Measure.map_congr
      filter_upwards [D.densityMeasure_ae_mem] with x hx
      exact D.quantileReal_cdf ⟨hx.1.le, hx.2.le⟩
    _ = D.densityMeasure := Measure.map_id

instance densityMeasure_isProbabilityMeasure : IsProbabilityMeasure D.densityMeasure := by
  let : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by
    simp [Real.volume_Ioo]⟩
  rw [← D.map_quantileReal_uniform]
  exact (Measure.isProbabilityMeasure_map_iff
    D.quantileReal_continuous.measurable.aemeasurable).2 inferInstance

lemma lintegral_quantileReal (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ s in Ioo (0 : ℝ) 1, f (D.quantileReal s)) = ∫⁻ x, f x ∂D.densityMeasure := by
  rw [← D.map_quantileReal_uniform,
    lintegral_map hf D.quantileReal_continuous.measurable]

lemma integral_quantileReal (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f D.densityMeasure) :
    (∫ s in Ioo (0 : ℝ) 1, f (D.quantileReal s)) = ∫ x, f x ∂D.densityMeasure := by
  rw [← D.map_quantileReal_uniform] at hf ⊢
  exact (integral_map D.quantileReal_continuous.measurable.aemeasurable hf).symm

/-- Inverse thresholds reduce parameter measurability to cumulative-integral evaluations. -/
lemma quantileReal_lt_iff {s r : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    D.quantileReal s < r ↔ D.lower < r ∧ (D.upper ≤ r ∨ s < D.cdf r) := by
  have hq := D.quantileReal_mem_interior hs
  have hc := D.cdf_quantileReal ⟨hs.1.le, hs.2.le⟩
  constructor
  · intro h
    refine ⟨hq.1.trans h, ?_⟩
    by_cases hr : D.upper ≤ r
    · exact Or.inl hr
    · right
      have hmono := D.cdf_strictMonoOn (D.quantileReal_mem s)
        ⟨(hq.1.trans h).le, (lt_of_not_ge hr).le⟩ h
      rwa [hc] at hmono
  · rintro ⟨hr0, hr1 | hr1⟩
    · exact hq.2.trans_le hr1
    · by_cases hr : D.upper ≤ r
      · exact hq.2.trans_le hr
      · apply (D.cdf_strictMonoOn.lt_iff_lt (D.quantileReal_mem s)
          ⟨hr0.le, (lt_of_not_ge hr).le⟩).mp
        rwa [hc]

/-- Measurable parameters give measurable interior quantiles. The density structures themselves
need no chosen measurable-space architecture: only endpoint and cumulative evaluations matter. -/
theorem measurable_quantileReal_family {Ω : Type*} [MeasurableSpace Ω]
    (D : Ω → PositiveIntervalDensity)
    (hlower : Measurable fun ω => (D ω).lower)
    (hupper : Measurable fun ω => (D ω).upper)
    (hcdf : ∀ r : ℝ, Measurable fun ω => (D ω).cdf r)
    {s : Ω → ℝ} (hs : Measurable s) (hsrange : ∀ ω, s ω ∈ Ioo (0 : ℝ) 1) :
    Measurable (fun ω => (D ω).quantileReal (s ω)) := by
  apply measurable_of_Iio
  intro r
  have heq : (fun ω => (D ω).quantileReal (s ω)) ⁻¹' Iio r =
      {ω | (D ω).lower < r} ∩
        ({ω | (D ω).upper ≤ r} ∪ {ω | s ω < (D ω).cdf r}) := by
    ext ω
    exact (D ω).quantileReal_lt_iff (hsrange ω)
  rw [heq]
  exact (measurableSet_lt hlower measurable_const).inter
    ((measurableSet_le hupper measurable_const).union (measurableSet_lt hs (hcdf r)))

/-- Joint Borel measurability of a family of quantiles on parameter × open unit interval. -/
theorem measurable_joint_quantileReal {Ω : Type*} [MeasurableSpace Ω]
    (D : Ω → PositiveIntervalDensity)
    (hlower : Measurable fun ω => (D ω).lower)
    (hupper : Measurable fun ω => (D ω).upper)
    (hcdf : ∀ r : ℝ, Measurable fun ω => (D ω).cdf r) :
    Measurable (fun z : Ω × Ioo (0 : ℝ) 1 => (D z.1).quantileReal z.2) := by
  apply measurable_quantileReal_family (fun z : Ω × Ioo (0 : ℝ) 1 => D z.1)
    (hlower.comp measurable_fst) (hupper.comp measurable_fst)
    (fun r => (hcdf r).comp measurable_fst)
    (measurable_subtype_coe.comp measurable_snd)
  exact fun z => z.2.2

/-- Parameter integrals over measurable moving real intervals are measurable. -/
lemma measurable_intervalIntegral_family {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω × ℝ → ℝ} (hf : Measurable f) {a b : Ω → ℝ}
    (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun ω => ∫ t in a ω..b ω, f (ω, t)) := by
  have hhalf (a b : Ω → ℝ) (ha : Measurable a) (hb : Measurable b) :
      Measurable (fun ω => ∫ t in Ioc (a ω) (b ω), f (ω, t)) := by
    let S : Set (Ω × ℝ) := {z | a z.1 < z.2 ∧ z.2 ≤ b z.1}
    have hS : MeasurableSet S :=
      (measurableSet_lt (ha.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hb.comp measurable_fst))
    have hi : Measurable (fun ω => ∫ t, S.indicator f (ω, t)) :=
      (hf.indicator hS).stronglyMeasurable.integral_prod_right'.measurable
    convert hi using 1
    funext ω
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      simp only [S, Set.indicator_apply, Set.mem_Ioc, Set.mem_ofPred_eq]
  exact (hhalf a b ha hb).sub (hhalf b a hb ha)

/-- Jointly measurable density data give jointly measurable quantiles, as required in each
recursive coordinate of a triangular inverse-CDF construction. -/
theorem measurable_joint_quantileReal_of_density {Ω : Type*} [MeasurableSpace Ω]
    (D : Ω → PositiveIntervalDensity)
    (hlower : Measurable fun ω => (D ω).lower)
    (hupper : Measurable fun ω => (D ω).upper)
    (hdensity : Measurable fun z : Ω × ℝ => (D z.1).density z.2) :
    Measurable (fun z : Ω × Ioo (0 : ℝ) 1 => (D z.1).quantileReal z.2) := by
  apply measurable_joint_quantileReal D hlower hupper
  intro r
  exact measurable_intervalIntegral_family hdensity hlower measurable_const

lemma quantileReal_of_nonpos {s : ℝ} (hs : s ≤ 0) : D.quantileReal s = D.lower := by
  have hzero : D.quantileReal 0 = D.lower := by
    simpa only [D.cdf_lower] using
      D.quantileReal_cdf (left_mem_Icc.mpr D.lower_lt_upper.le)
  calc
    D.quantileReal s = D.quantileReal 0 := by
      unfold quantileReal
      rw [Set.projIcc_of_le_left _ hs, Set.projIcc_left]
    _ = D.lower := hzero

lemma quantileReal_of_one_le {s : ℝ} (hs : 1 ≤ s) : D.quantileReal s = D.upper := by
  have hone : D.quantileReal 1 = D.upper := by
    simpa only [D.cdf_upper] using
      D.quantileReal_cdf (right_mem_Icc.mpr D.lower_lt_upper.le)
  calc
    D.quantileReal s = D.quantileReal 1 := by
      unfold quantileReal
      rw [Set.projIcc_of_right_le _ hs, Set.projIcc_right]
    _ = D.upper := hone

/-- The continuous extensions are jointly measurable even for parameters outside (0,1). -/
theorem measurable_quantileReal_family_global {Ω : Type*} [MeasurableSpace Ω]
    (D : Ω → PositiveIntervalDensity)
    (hlower : Measurable fun ω => (D ω).lower)
    (hupper : Measurable fun ω => (D ω).upper)
    (hcdf : ∀ r : ℝ, Measurable fun ω => (D ω).cdf r)
    {s : Ω → ℝ} (hs : Measurable s) :
    Measurable (fun ω => (D ω).quantileReal (s ω)) := by
  apply measurable_of_Iio
  intro r
  have heq : (fun ω => (D ω).quantileReal (s ω)) ⁻¹' Iio r =
      ({ω | s ω ≤ 0} ∩ {ω | (D ω).lower < r}) ∪
      ({ω | 1 ≤ s ω} ∩ {ω | (D ω).upper < r}) ∪
      ({ω | 0 < s ω} ∩ {ω | s ω < 1} ∩ {ω | (D ω).lower < r} ∩
        ({ω | (D ω).upper ≤ r} ∪ {ω | s ω < (D ω).cdf r})) := by
    ext ω
    by_cases h0 : s ω ≤ 0
    · have h1 : ¬ 1 ≤ s ω := by linarith
      simp [h0, h1, not_lt.mpr h0, (D ω).quantileReal_of_nonpos h0]
    · by_cases h1 : 1 ≤ s ω
      · simp [h0, h1, not_lt.mpr h1, (D ω).quantileReal_of_one_le h1]
      · have hsi : s ω ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_not_ge h0, lt_of_not_ge h1⟩
        simpa [h0, h1, hsi.1, hsi.2] using (D ω).quantileReal_lt_iff hsi (r := r)
  rw [heq]
  exact (((measurableSet_le hs measurable_const).inter
    (measurableSet_lt hlower measurable_const)).union
      ((measurableSet_le measurable_const hs).inter
        (measurableSet_lt hupper measurable_const))).union
    ((((measurableSet_lt measurable_const hs).inter
        (measurableSet_lt hs measurable_const)).inter
          (measurableSet_lt hlower measurable_const)).inter
      ((measurableSet_le hupper measurable_const).union
        (measurableSet_lt hs (hcdf r))))

theorem measurable_joint_quantileReal_global {Ω : Type*} [MeasurableSpace Ω]
    (D : Ω → PositiveIntervalDensity)
    (hlower : Measurable fun ω => (D ω).lower)
    (hupper : Measurable fun ω => (D ω).upper)
    (hdensity : Measurable fun z : Ω × ℝ => (D z.1).density z.2) :
    Measurable (fun z : Ω × ℝ => (D z.1).quantileReal z.2) := by
  apply measurable_quantileReal_family_global (fun z : Ω × ℝ => D z.1)
    (hlower.comp measurable_fst) (hupper.comp measurable_fst)
    _ measurable_snd
  intro r
  exact (measurable_intervalIntegral_family hdensity hlower measurable_const).comp measurable_fst

/-- One recursive sampling step has precisely the prescribed conditional density law. -/
theorem lintegral_joint_quantileReal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (D : Ω → PositiveIntervalDensity)
    (hlower : Measurable fun ω => (D ω).lower)
    (hupper : Measurable fun ω => (D ω).upper)
    (hdensity : Measurable fun z : Ω × ℝ => (D z.1).density z.2)
    (f : Ω × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f (z.1, (D z.1).quantileReal z.2)
      ∂μ.prod (volume.restrict (Ioo (0 : ℝ) 1))) =
        ∫⁻ ω, ∫⁻ x, f (ω, x) ∂(D ω).densityMeasure ∂μ := by
  have hQ := measurable_joint_quantileReal_global D hlower hupper hdensity
  have hm : Measurable (fun z : Ω × ℝ => f (z.1, (D z.1).quantileReal z.2)) :=
    hf.comp (measurable_fst.prodMk hQ)
  rw [lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr
  intro ω
  exact (D ω).lintegral_quantileReal (fun x => f (ω, x))
    (hf.comp (measurable_const.prodMk measurable_id))

lemma quantileReal_strictMonoOn : StrictMonoOn D.quantileReal (Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  by_contra h
  have hle : D.quantileReal t ≤ D.quantileReal s := le_of_not_gt h
  have hc := D.cdf_strictMonoOn.monotoneOn (D.quantileReal_mem t)
    (D.quantileReal_mem s) hle
  rw [D.cdf_quantileReal ht, D.cdf_quantileReal hs] at hc
  exact (not_le_of_gt hst) hc

/-- Conditional densities only need to exist on the measurable set of valid prefixes.
Their quantiles extend to a globally measurable map without imposing any density law
at the invalid prefixes. The extension agrees at every real argument on valid fibers. -/
theorem exists_measurable_quantile_extension {Ω : Type*} [MeasurableSpace Ω]
    (S : Set Ω) (hS : MeasurableSet S) (D : S → PositiveIntervalDensity)
    (hlower : Measurable fun ω => (D ω).lower)
    (hupper : Measurable fun ω => (D ω).upper)
    (hdensity : Measurable fun z : S × ℝ => (D z.1).density z.2) :
    ∃ Q : Ω × ℝ → ℝ, Measurable Q ∧
      (∀ ω : S, ∀ s : ℝ, Q (ω, s) = (D ω).quantileReal s) ∧
      (∀ ω : S, Measure.map (fun s => Q (ω, s))
        (volume.restrict (Ioo (0 : ℝ) 1)) = (D ω).densityMeasure) ∧
      (∀ ω : S, ∀ s ∈ Ioo (0 : ℝ) 1,
        HasDerivAt (fun t => Q (ω, t)) ((D ω).density (Q (ω, s)))⁻¹ s) ∧
      (∀ ω : S, StrictMonoOn (fun s => Q (ω, s)) (Icc (0 : ℝ) 1)) := by
  have hQ₀ := measurable_joint_quantileReal_global D hlower hupper hdensity
  have hemb : MeasurableEmbedding (Prod.map (Subtype.val : S → Ω) (id : ℝ → ℝ)) :=
    (MeasurableEmbedding.subtype_coe hS).prodMap MeasurableEmbedding.id
  obtain ⟨Q, hQ, hext⟩ := hemb.exists_measurable_extend hQ₀ (fun _ => inferInstance)
  have hmatch (ω : S) (s : ℝ) : Q (ω, s) = (D ω).quantileReal s :=
    congrFun hext (ω, s)
  refine ⟨Q, hQ, hmatch, ?_, ?_, ?_⟩
  · intro ω
    have heq : (fun s => Q (ω, s)) = (D ω).quantileReal := funext (hmatch ω)
    rw [heq]
    exact (D ω).map_quantileReal_uniform
  · intro ω s hs
    have heq : (fun t => Q (ω, t)) = (D ω).quantileReal := funext (hmatch ω)
    rw [heq, hmatch ω s]
    exact (D ω).quantileReal_hasDerivAt hs
  · intro ω
    have heq : (fun s => Q (ω, s)) = (D ω).quantileReal := funext (hmatch ω)
    rw [heq]
    exact (D ω).quantileReal_strictMonoOn

end PositiveIntervalDensity
end Problem358

end

end OAI
