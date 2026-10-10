import Mathlib

namespace OAI

/-! Three-dimensional cylinder averages, fixed-scale maximal bounds and finite weighted sampling. -/

open MeasureTheory
open scoped ENNReal

namespace Kakeya

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Direction := ↥(Metric.sphere (0 : Space) 1)

noncomputable def surfaceMeasure : Measure Direction :=
  (volume : Measure Space).toSphere

def tube (δ : ℝ) (a : Space) (ω : Direction) : Set Space :=
  {x | ∃ t : ℝ, |t| ≤ (1 : ℝ) / 2 ∧
    ∃ u : Space, inner ℝ u (ω : Space) = 0 ∧ ‖u‖ ≤ δ ∧
      x = a + t • (ω : Space) + u}

noncomputable def tubeAverage (δ : ℝ) (f : Space → ℂ)
    (a : Space) (ω : Direction) : ℝ≥0∞ :=
  (ENNReal.ofReal (Real.pi * δ ^ 2))⁻¹ *
    ∫⁻ x in tube δ a ω, ENNReal.ofReal ‖f x‖ ∂volume

noncomputable def maximal (δ : ℝ) (f : Space → ℂ) (ω : Direction) : ℝ≥0∞ :=
  ⨆ a : Space, tubeAverage δ f a ω

def MaximalConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ f : Space → ℂ,
      MemLp f (3 : ℝ≥0∞) (volume : Measure Space) →
      MemLp (maximal δ f) (3 : ℝ≥0∞) surfaceMeasure ∧
      eLpNorm (maximal δ f) (3 : ℝ≥0∞) surfaceMeasure ≤
        ENNReal.ofReal (C * δ ^ (-ε)) *
          eLpNorm f (3 : ℝ≥0∞) (volume : Measure Space)

open Set

theorem direction_norm (ω : Direction) : ‖(ω : Space)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using ω.property

theorem direction_inner (ω : Direction) : inner ℝ (ω : Space) (ω : Space) = 1 := by
  simp

theorem mem_tube_iff (δ : ℝ) (a x : Space) (ω : Direction) :
    x ∈ tube δ a ω ↔
      |inner ℝ (x - a) (ω : Space)| ≤ (1 : ℝ) / 2 ∧
      ‖x - a - (inner ℝ (x - a) (ω : Space)) • (ω : Space)‖ ≤ δ := by
  constructor
  · rintro ⟨t, ht, u, hu, hud, rfl⟩
    have heq : a + t • (ω : Space) + u - a = t • (ω : Space) + u := by abel
    rw [heq]
    simp only [inner_add_left, inner_smul_left, direction_inner, hu]
    simpa using And.intro ht hud
  · rintro ⟨ht, hu⟩
    refine ⟨inner ℝ (x-a) (ω : Space), ht,
      x - a - inner ℝ (x-a) (ω : Space) • (ω : Space), ?_, hu, ?_⟩
    · simp [inner_sub_left, inner_smul_left]
    · abel

theorem isClosed_tube (δ : ℝ) (a : Space) (ω : Direction) :
    IsClosed (tube δ a ω) := by
  have h : tube δ a ω =
      {x | |inner ℝ (x - a) (ω : Space)| ≤ (1 : ℝ)/2} ∩
      {x | ‖x-a-inner ℝ (x-a) (ω : Space) • (ω : Space)‖ ≤ δ} := by
    ext x
    exact mem_tube_iff δ a x ω
  rw [h]
  exact (isClosed_le (by fun_prop) continuous_const).inter
    (isClosed_le (by fun_prop) continuous_const)

theorem measurableSet_tube (δ : ℝ) (a : Space) (ω : Direction) :
    MeasurableSet (tube δ a ω) := (isClosed_tube δ a ω).measurableSet

abbrev axis (ω : Direction) : Submodule ℝ Space := ℝ ∙ (ω : Space)

theorem direction_ne_zero (ω : Direction) : (ω : Space) ≠ 0 := by
  intro h
  have := direction_norm ω
  simp [h] at this

theorem finrank_axis (ω : Direction) : Module.finrank ℝ (axis ω) = 1 :=
  finrank_span_singleton (direction_ne_zero ω)

theorem finrank_plane (ω : Direction) : Module.finrank ℝ (axis ω)ᗮ = 2 := by
  have h := (axis ω).finrank_add_finrank_orthogonal
  rw [finrank_axis] at h
  have hdim : Module.finrank ℝ Space = 3 := by simp [Space]
  omega

theorem axis_projection (ω : Direction) (x : Space) :
    (axis ω).starProjection x = inner ℝ x (ω : Space) • (ω : Space) := by
  rw [Submodule.starProjection_unit_singleton ℝ (direction_norm ω), real_inner_comm]

noncomputable def cylinderCoordinates (ω : Direction) :
    Space → (axis ω) × (axis ω)ᗮ :=
  fun x => WithLp.ofLp ((axis ω).orthogonalDecomposition x)

theorem cylinderCoordinates_measurePreserving (ω : Direction) :
    MeasurePreserving (cylinderCoordinates ω) :=
  (WithLp.volume_preserving_ofLp (axis ω) (axis ω)ᗮ).comp
    (axis ω).orthogonalDecomposition.measurePreserving

theorem tube_zero_eq_preimage (δ : ℝ) (ω : Direction) :
    tube δ 0 ω = (cylinderCoordinates ω) ⁻¹'
      (Metric.closedBall 0 ((1 : ℝ)/2) ×ˢ Metric.closedBall 0 δ) := by
  ext x
  rw [mem_tube_iff]
  simp only [sub_zero, mem_preimage, mem_prod, Metric.mem_closedBall, dist_zero_right]
  simp only [cylinderCoordinates, Submodule.orthogonalDecomposition_apply, WithLp.ofLp_toLp]
  change _ ↔ ‖(axis ω).orthogonalProjectionOnto x‖ ≤ (1 : ℝ)/2 ∧
    ‖(axis ω)ᗮ.orthogonalProjectionOnto x‖ ≤ δ
  change _ ↔ ‖(axis ω).starProjection x‖ ≤ (1 : ℝ)/2 ∧
    ‖(axis ω)ᗮ.starProjection x‖ ≤ δ
  rw [Submodule.starProjection_orthogonal_val, axis_projection]
  simp [norm_smul, Real.norm_eq_abs]

theorem volume_axis_closedBall (ω : Direction) :
    volume (Metric.closedBall (0 : axis ω) ((1 : ℝ)/2)) = 1 := by
  rw [InnerProductSpace.volume_closedBall_of_dim_odd (k := 0) (by simp [finrank_axis])]
  norm_num [finrank_axis, ENNReal.ofReal_div_of_pos, ENNReal.inv_mul_cancel]

theorem volume_plane_closedBall (ω : Direction) (δ : ℝ) (hδ : 0 ≤ δ) :
    volume (Metric.closedBall (0 : (axis ω)ᗮ) δ) = ENNReal.ofReal (Real.pi * δ^2) := by
  have : Nontrivial (axis ω)ᗮ := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [finrank_plane]; norm_num)
  rw [InnerProductSpace.volume_closedBall_of_dim_even (k := 1) (by simp [finrank_plane])]
  simp only [finrank_plane, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
  rw [ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hδ, mul_comm]

theorem volume_tube_zero (δ : ℝ) (ω : Direction) (hδ : 0 ≤ δ) :
    volume (tube δ 0 ω) = ENNReal.ofReal (Real.pi * δ^2) := by
  rw [tube_zero_eq_preimage]
  rw [(cylinderCoordinates_measurePreserving ω).measure_preimage
    (MeasurableSet.prod measurableSet_closedBall measurableSet_closedBall).nullMeasurableSet]
  rw [Measure.volume_eq_prod, Measure.prod_prod, volume_axis_closedBall, volume_plane_closedBall ω δ hδ, one_mul]
theorem tube_translate_preimage (δ : ℝ) (a : Space) (ω : Direction) :
    (fun x : Space => a + x) ⁻¹' tube δ a ω = tube δ 0 ω := by
  ext x
  simp only [mem_preimage, mem_tube_iff, add_sub_cancel_left, sub_zero]

theorem volume_tube (δ : ℝ) (a : Space) (ω : Direction) (hδ : 0 ≤ δ) :
    volume (tube δ a ω) = ENNReal.ofReal (Real.pi * δ^2) := by
  rw [← (measurePreserving_add_left (volume : Measure Space) a).measure_preimage
    (measurableSet_tube δ a ω).nullMeasurableSet, tube_translate_preimage]
  exact volume_tube_zero δ ω hδ

theorem tubeAverage_le_holder {δ : ℝ} (hδ : 0 < δ) {f : Space → ℂ}
    (hf : MemLp f (3 : ℝ≥0∞) (volume : Measure Space)) (a : Space) (ω : Direction) :
    tubeAverage δ f a ω ≤ (ENNReal.ofReal (Real.pi * δ^2)) ^ (-(1 : ℝ)/3) *
      eLpNorm f (3 : ℝ≥0∞) (volume : Measure Space) := by
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.pi * δ^2)
  have hc : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have hc' : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hrestrict := hf.mono_measure (Measure.restrict_le_self (s := tube δ a ω))
  have hh := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := (1 : ℝ≥0∞))
    (q := (3 : ℝ≥0∞)) (by norm_num) hrestrict.aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm hrestrict.aestronglyMeasurable,
    Measure.restrict_apply_univ,
    volume_tube δ a ω hδ.le] at hh
  have hh' : (∫⁻ x in tube δ a ω, ENNReal.ofReal ‖f x‖ ∂volume) ≤
      eLpNorm f (3 : ℝ≥0∞) (volume : Measure Space) * c ^ ((2 : ℝ)/3) := by
    simp only [ofReal_norm]
    refine hh.trans ?_
    norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat, one_div_one] 
    convert mul_le_mul_left (eLpNorm_mono_measure f
      (Measure.restrict_le_self (s := tube δ a ω))) (c ^ ((2 : ℝ)/3)) using 1
  calc
    tubeAverage δ f a ω ≤ c⁻¹ *
        (eLpNorm f (3 : ℝ≥0∞) volume * c ^ ((2 : ℝ)/3)) := mul_le_mul_right hh' _
    _ = (c ^ (-1 : ℝ) * c ^ ((2 : ℝ)/3)) * eLpNorm f (3 : ℝ≥0∞) volume := by
      rw [ENNReal.rpow_neg_one]; ac_rfl
    _ = c ^ (-(1 : ℝ)/3) * eLpNorm f (3 : ℝ≥0∞) volume := by
      rw [← ENNReal.rpow_add _ _ hc hc']; norm_num

theorem maximal_le_holder {δ : ℝ} (hδ : 0 < δ) {f : Space → ℂ}
    (hf : MemLp f (3 : ℝ≥0∞) (volume : Measure Space)) (ω : Direction) :
    maximal δ f ω ≤ (ENNReal.ofReal (Real.pi * δ^2)) ^ (-(1 : ℝ)/3) *
      eLpNorm f (3 : ℝ≥0∞) (volume : Measure Space) :=
  iSup_le (fun a => tubeAverage_le_holder hδ hf a ω)

theorem cylinderCoordinates_norm_fst (ω : Direction) (x : Space) :
    ‖(cylinderCoordinates ω x).1‖ = |inner ℝ x (ω : Space)| := by
  simp only [cylinderCoordinates, Submodule.orthogonalDecomposition_apply, WithLp.ofLp_toLp]
  change ‖(axis ω).starProjection x‖ = _
  rw [axis_projection]
  simp [norm_smul, Real.norm_eq_abs]

theorem cylinderCoordinates_norm_snd (ω : Direction) (x : Space) :
    ‖(cylinderCoordinates ω x).2‖ =
      ‖x - inner ℝ x (ω : Space) • (ω : Space)‖ := by
  simp only [cylinderCoordinates, Submodule.orthogonalDecomposition_apply, WithLp.ofLp_toLp]
  change ‖(axis ω)ᗮ.starProjection x‖ = _
  rw [Submodule.starProjection_orthogonal_val, axis_projection]

theorem ae_cylinderBoundary_ne (δ : ℝ) (a : Space) (ω : Direction) :
    ∀ᵐ x : Space ∂volume,
      |inner ℝ (x-a) (ω : Space)| ≠ (1 : ℝ)/2 ∧
      ‖x-a-inner ℝ (x-a) (ω : Space) • (ω : Space)‖ ≠ δ := by
  have hmp : MeasurePreserving (fun x : Space => cylinderCoordinates ω (x-a)) := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      (cylinderCoordinates_measurePreserving ω).comp
        (measurePreserving_add_right (volume : Measure Space) (-a))
  have haxis : ∀ᵐ x : Space ∂volume, |inner ℝ (x-a) (ω : Space)| ≠ (1 : ℝ)/2 := by
    rw [ae_iff]
    simp only [not_not]
    have hset : {x : Space | |inner ℝ (x-a) (ω : Space)| = (1 : ℝ)/2} =
        (fun x : Space => cylinderCoordinates ω (x-a)) ⁻¹'
          (Metric.sphere 0 ((1 : ℝ)/2) ×ˢ (univ : Set (axis ω)ᗮ)) := by
      ext x
      simp only [mem_ofPred_eq, mem_preimage, mem_prod, mem_univ, Metric.mem_sphere, dist_zero_right, and_true,
        cylinderCoordinates_norm_fst]
    rw [hset, hmp.measure_preimage
      (Metric.isClosed_sphere.measurableSet.prod MeasurableSet.univ).nullMeasurableSet,
      Measure.volume_eq_prod, Measure.prod_prod,
      Measure.addHaar_sphere_of_ne_zero _ _ (by norm_num : (1 : ℝ)/2 ≠ 0), zero_mul]
  have hplane : ∀ᵐ x : Space ∂volume,
      ‖x-a-inner ℝ (x-a) (ω : Space) • (ω : Space)‖ ≠ δ := by
    have : Nontrivial (axis ω)ᗮ := Module.nontrivial_of_finrank_pos (R := ℝ)
      (by rw [finrank_plane]; norm_num)
    rw [ae_iff]
    simp only [not_not]
    have hset : {x : Space | ‖x-a-inner ℝ (x-a) (ω : Space) • (ω : Space)‖ = δ} =
        (fun x : Space => cylinderCoordinates ω (x-a)) ⁻¹'
          ((univ : Set (axis ω)) ×ˢ Metric.sphere 0 δ) := by
      ext x
      simp only [mem_ofPred_eq, mem_preimage, mem_prod, mem_univ, Metric.mem_sphere, dist_zero_right, true_and,
        cylinderCoordinates_norm_snd]
    rw [hset, hmp.measure_preimage
      (MeasurableSet.univ.prod Metric.isClosed_sphere.measurableSet).nullMeasurableSet,
      Measure.volume_eq_prod, Measure.prod_prod, Measure.addHaar_sphere, mul_zero]
  filter_upwards [haxis, hplane] with x hx hy
  exact ⟨hx, hy⟩

theorem eventually_le_iff_of_ne {α : Type*} [TopologicalSpace α] {g : α → ℝ}
    {p : α} {r : ℝ} (hg : ContinuousAt g p) (h : g p ≠ r) :
    ∀ᶠ q in nhds p, (g q ≤ r ↔ g p ≤ r) := by
  rcases h.lt_or_gt with hlt | hgt
  · filter_upwards [hg.eventually (Iio_mem_nhds hlt)] with q hq
    exact iff_of_true hq.le hlt.le
  · filter_upwards [hg.eventually (Ioi_mem_nhds hgt)] with q hq
    exact iff_of_false (not_le.mpr hq) (not_le.mpr hgt)

theorem ae_tendsto_tubeIndicator (δ : ℝ) (p : Space × Direction) (g : Space → ℝ≥0∞) :
    ∀ᵐ x : Space ∂volume, Filter.Tendsto
      (fun q : Space × Direction => (tube δ q.1 q.2).indicator g x)
      (nhds p) (nhds ((tube δ p.1 p.2).indicator g x)) := by
  classical
  filter_upwards [ae_cylinderBoundary_ne δ p.1 p.2] with x hx
  have ht₁ : ∀ᶠ q : Space × Direction in nhds p,
      (|inner ℝ (x-q.1) (q.2 : Space)| ≤ (1 : ℝ)/2 ↔
        |inner ℝ (x-p.1) (p.2 : Space)| ≤ (1 : ℝ)/2) :=
    eventually_le_iff_of_ne (by fun_prop) hx.1
  have ht₂ : ∀ᶠ q : Space × Direction in nhds p,
      (‖x-q.1-inner ℝ (x-q.1) (q.2 : Space) • (q.2 : Space)‖ ≤ δ ↔
        ‖x-p.1-inner ℝ (x-p.1) (p.2 : Space) • (p.2 : Space)‖ ≤ δ) :=
    eventually_le_iff_of_ne (by fun_prop) hx.2
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [ht₁, ht₂] with q hq₁ hq₂
  have heq : x ∈ tube δ q.1 q.2 ↔ x ∈ tube δ p.1 p.2 := by
    simp only [mem_tube_iff, hq₁, hq₂]
  simp only [Set.indicator_apply, heq]

theorem tube_subset_closedBall {δ R : ℝ} {a : Space} (ha : ‖a‖ ≤ R) (ω : Direction) :
    tube δ a ω ⊆ Metric.closedBall (0 : Space) (R + (1 : ℝ)/2 + δ) := by
  rintro x ⟨t, ht, u, _, hu, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  calc
    ‖a + t • (ω : Space) + u‖ ≤ ‖a‖ + ‖t • (ω : Space)‖ + ‖u‖ :=
      (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ = ‖a‖ + |t| + ‖u‖ := by simp [norm_smul, Real.norm_eq_abs]
    _ ≤ R + (1 : ℝ)/2 + δ := by gcongr

theorem integrableOn_closedBall_of_memLp {f : Space → ℂ}
    (hf : MemLp f (3 : ℝ≥0∞) (volume : Measure Space)) (R : ℝ) :
    IntegrableOn f (Metric.closedBall 0 R) volume := by
  have : IsFiniteMeasure ((volume : Measure Space).restrict (Metric.closedBall 0 R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Space) R).measure_ne_top
  exact (hf.mono_measure Measure.restrict_le_self).integrable (by norm_num)

theorem continuous_tubeIntegral (δ : ℝ) {f : Space → ℂ}
    (hf : MemLp f (3 : ℝ≥0∞) (volume : Measure Space)) :
    Continuous (fun p : Space × Direction =>
      ∫⁻ x in tube δ p.1 p.2, ENNReal.ofReal ‖f x‖ ∂volume) := by
  classical
  rw [continuous_iff_continuousAt]
  intro p
  let R : ℝ := ‖p.1‖ + 1 + (1 : ℝ)/2 + δ
  let g : Space → ℝ≥0∞ := fun x => ENNReal.ofReal ‖f x‖
  let bound : Space → ℝ≥0∞ := (Metric.closedBall 0 R).indicator g
  have hg : AEMeasurable g (volume : Measure Space) :=
    hf.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal
  have hF : ∀ᶠ q : Space × Direction in nhds p,
      AEMeasurable ((tube δ q.1 q.2).indicator g) (volume : Measure Space) :=
    Filter.Eventually.of_forall (fun q => hg.indicator (measurableSet_tube δ q.1 q.2))
  have hb : ∀ᶠ q : Space × Direction in nhds p,
      ∀ᵐ x : Space ∂volume, (tube δ q.1 q.2).indicator g x ≤ bound x := by
    have hn : ∀ᶠ q : Space × Direction in nhds p, ‖q.1‖ < ‖p.1‖ + 1 :=
      (continuous_fst.norm.continuousAt).eventually (Iio_mem_nhds (by linarith))
    filter_upwards [hn] with q hq
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x ∈ tube δ q.1 q.2
    · have hxB : x ∈ Metric.closedBall 0 R := tube_subset_closedBall hq.le q.2 hx
      simp only [bound, indicator_of_mem hx, indicator_of_mem hxB, le_refl]
    · simp only [indicator_of_notMem hx, zero_le]
  have hfin : (∫⁻ x, bound x ∂volume) ≠ ∞ := by
    rw [lintegral_indicator measurableSet_closedBall]
    simpa only [g, ofReal_norm] using
      (integrableOn_closedBall_of_memLp hf R).hasFiniteIntegral.ne
  have ht := tendsto_lintegral_filter_of_dominated_convergence' bound hF hb hfin
    (ae_tendsto_tubeIndicator δ p g)
  simpa only [g, ContinuousAt, lintegral_indicator (measurableSet_tube δ _ _)] using ht

theorem continuous_tubeAverage {δ : ℝ} (hδ : 0 < δ) {f : Space → ℂ}
    (hf : MemLp f (3 : ℝ≥0∞) (volume : Measure Space)) :
    Continuous (fun p : Space × Direction => tubeAverage δ f p.1 p.2) := by
  have hc : (ENNReal.ofReal (Real.pi * δ^2))⁻¹ ≠ ∞ := by
    simp only [ne_eq, ENNReal.inv_eq_top, ENNReal.ofReal_eq_zero]
    exact not_le.mpr (by positivity)
  exact (ENNReal.continuous_const_mul hc).comp (continuous_tubeIntegral δ hf)

theorem lowerSemicontinuous_maximal {δ : ℝ} (hδ : 0 < δ) {f : Space → ℂ}
    (hf : MemLp f (3 : ℝ≥0∞) (volume : Measure Space)) :
    LowerSemicontinuous (maximal δ f) := by
  apply lowerSemicontinuous_iSup
  intro a
  exact ((continuous_tubeAverage hδ hf).comp
    (continuous_const.prodMk continuous_id)).lowerSemicontinuous

theorem measurable_maximal {δ : ℝ} (hδ : 0 < δ) {f : Space → ℂ}
    (hf : MemLp f (3 : ℝ≥0∞) (volume : Measure Space)) :
    Measurable (maximal δ f) := (lowerSemicontinuous_maximal hδ hf).measurable

theorem memLp_maximal {δ : ℝ} (hδ : 0 < δ) {f : Space → ℂ}
    (hf : MemLp f (3 : ℝ≥0∞) (volume : Measure Space)) :
    MemLp (maximal δ f) (3 : ℝ≥0∞) surfaceMeasure := by
  let : IsFiniteMeasure surfaceMeasure := by
    unfold surfaceMeasure
    infer_instance
  have hc : ENNReal.ofReal (Real.pi * δ^2) ≠ 0 := by positivity
  have hb : (ENNReal.ofReal (Real.pi * δ^2)) ^ (-(1 : ℝ)/3) *
      eLpNorm f (3 : ℝ≥0∞) (volume : Measure Space) ≠ ∞ := by
    have hf' := hf.eLpNorm_lt_top
    finiteness
  exact MemLp.of_enorm_bound (measurable_maximal hδ hf).aestronglyMeasurable hb
    (Filter.Eventually.of_forall (maximal_le_holder hδ hf))

end Kakeya

namespace Kakeya

theorem maximal_real_smul (δ c : ℝ) (f : Space → ℂ) (ω : Direction) :
    maximal δ (c • f) ω=ENNReal.ofReal |c| *maximal δ f ω := by
  unfold maximal tubeAverage
  simp_rw [Pi.smul_apply,norm_smul,Real.norm_eq_abs,ENNReal.ofReal_mul (abs_nonneg c)]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [ENNReal.mul_iSup]
  congr 1
  funext a
  ring

lemma eLpNorm_cube_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℝ≥0∞) :
    eLpNorm' g 3 μ ^ (3:ℕ)=∫⁻ x,g x^3 ∂μ := by
  simpa only [ENNReal.rpow_ofNat, enorm_eq_self] using
    (lintegral_rpow_enorm_eq_rpow_eLpNorm' (f := g) (μ := μ)
      (by norm_num : (0 : ℝ) < 3)).symm

lemma eLpNorm_ennreal_mul {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (c : ℝ≥0∞) (hc : c≠∞) (g : α → ℝ≥0∞) :
    eLpNorm' (fun x=>c*g x) 3 μ=c*eLpNorm' g 3 μ := by
  apply (ENNReal.pow_right_strictMono (by norm_num : (3:ℕ)≠0)).injective
  simp only [mul_pow,eLpNorm_cube_eq]
  exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top hc)

theorem maximal_bound_of_normalized {δ : ℝ} (hδ : 0<δ) (B : ℝ≥0∞)
    (hB : ∀ f : Space → ℂ,MemLp f 3 volume → eLpNorm f 3 volume≤1 →
      eLpNorm (maximal δ f) 3 surfaceMeasure≤B) :
    ∀ f : Space → ℂ,MemLp f 3 volume →
      eLpNorm (maximal δ f) 3 surfaceMeasure≤B*eLpNorm f 3 volume := by
  intro f hf
  by_cases hz : eLpNorm f 3 volume=0
  · have hM : maximal δ f=0 := by
      funext ω
      exact le_bot_iff.mp (by simpa [hz] using maximal_le_holder hδ hf ω)
    simp [hM,hz]
  let n : ℝ := (eLpNorm f 3 volume).toReal
  have hn : 0<n := ENNReal.toReal_pos hz hf.eLpNorm_lt_top.ne
  have hne : ENNReal.ofReal n=eLpNorm f 3 volume := ENNReal.ofReal_toReal hf.eLpNorm_lt_top.ne
  let g : Space → ℂ := n⁻¹ • f
  have hg : MemLp g 3 volume := hf.const_smul _
  have hnorm : eLpNorm g 3 volume=1 := by
    change eLpNorm (n⁻¹ • f) 3 volume=1
    rw [eLpNorm_const_smul,← ofReal_norm,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),
      ENNReal.ofReal_inv_of_pos hn,hne,ENNReal.inv_mul_cancel hz hf.eLpNorm_lt_top.ne]
  have hfg : f=n • g := by
    dsimp [g]
    rw [smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
  calc
    eLpNorm (maximal δ f) 3 surfaceMeasure =
        ENNReal.ofReal n*eLpNorm (maximal δ g) 3 surfaceMeasure := by
      have hM : maximal δ f=fun ω=>ENNReal.ofReal n*maximal δ g ω := by
        funext ω
        calc
          maximal δ f ω=maximal δ (n • g) ω := congrArg (fun u=>maximal δ u ω) hfg
          _ = _ := by rw [maximal_real_smul,abs_of_pos hn]
      rw [eLpNorm_eq_eLpNorm' (by norm_num : (3 : ℝ≥0∞) ≠ 0) (by norm_num)
        (measurable_maximal hδ hf).aestronglyMeasurable,
        eLpNorm_eq_eLpNorm' (by norm_num : (3 : ℝ≥0∞) ≠ 0) (by norm_num)
        (measurable_maximal hδ hg).aestronglyMeasurable,
        ENNReal.toReal_ofNat, hM]
      exact eLpNorm_ennreal_mul _ _ ENNReal.ofReal_ne_top _
    _ ≤ ENNReal.ofReal n*B := mul_le_mul' le_rfl (hB g hg hnorm.le)
    _ = _ := by rw [hne,mul_comm]
end Kakeya

namespace Kakeya

lemma surfaceMeasure_univ :
    surfaceMeasure Set.univ = ENNReal.ofReal (4 * Real.pi) := by
  rw [surfaceMeasure, Measure.toSphere_apply_univ,
    InnerProductSpace.volume_ball_of_dim_odd (k := 1) (by simp [Space])]
  norm_num [Space]
  rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num,
    show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  congr 1
  ring

theorem tubeAverage_congr_ae (δ : ℝ) {f g : Space → ℂ}
    (hfg : f =ᵐ[volume] g) (a : Space) (ω : Direction) :
    tubeAverage δ f a ω = tubeAverage δ g a ω := by
  unfold tubeAverage
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hfg] with x hx
  rw [hx]

theorem maximal_congr_ae (δ : ℝ) {f g : Space → ℂ}
    (hfg : f =ᵐ[volume] g) : maximal δ f = maximal δ g := by
  funext ω
  unfold maximal
  congr 1
  funext a
  exact tubeAverage_congr_ae δ hfg a ω

theorem maximal_norm_le_holder {δ : ℝ} (hδ : 0 < δ) {f : Space → ℂ}
    (hf : MemLp f (3 : ℝ≥0∞) (volume : Measure Space)) :
    eLpNorm (maximal δ f) (3 : ℝ≥0∞) surfaceMeasure ≤
      (ENNReal.ofReal (4 * Real.pi)) ^ ((1 : ℝ) / 3) *
        (ENNReal.ofReal (Real.pi * δ ^ 2)) ^ (-(1 : ℝ) / 3) *
          eLpNorm f (3 : ℝ≥0∞) (volume : Measure Space) := by
  let b : ℝ≥0∞ := (ENNReal.ofReal (Real.pi * δ ^ 2)) ^ (-(1 : ℝ) / 3) *
    eLpNorm f (3 : ℝ≥0∞) (volume : Measure Space)
  calc
    eLpNorm (maximal δ f) (3 : ℝ≥0∞) surfaceMeasure ≤
        eLpNorm (fun _ : Direction => b) (3 : ℝ≥0∞) surfaceMeasure := by
      apply eLpNorm_mono_enorm (measurable_maximal hδ hf).aestronglyMeasurable
      intro ω
      simpa only [enorm_eq_self] using maximal_le_holder hδ hf ω
    _ = b * (surfaceMeasure Set.univ) ^ ((1 : ℝ) / 3) := by
      rw [eLpNorm_const' b (by norm_num) (by norm_num)]
      simp only [enorm_eq_self, ENNReal.toReal_ofNat]
    _ = _ := by rw [surfaceMeasure_univ]; dsimp only [b]; ac_rfl

end Kakeya

open scoped BigOperators

namespace Kakeya.WeightedConvex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def trialMass (p : ι → ℝ) (σ : ι → Bool) : ℝ :=
  ∏ i, if σ i then p i else 1 - p i

def selected (σ : ι → Bool) : Finset ι :=
  Finset.univ.filter fun i => σ i = true

def trialCount (A : Finset ι) (σ : ι → Bool) : ℝ :=
  ∑ i ∈ A, if σ i then 1 else 0

lemma trialCount_eq_card (A : Finset ι) (σ : ι → Bool) :
    trialCount A σ = ((selected σ ∩ A).card : ℝ) := by
  rw [trialCount, Finset.sum_boole]
  congr 1
  apply congrArg Finset.card
  ext i
  simp [selected, and_comm]

omit [DecidableEq ι] in
lemma trialMass_nonneg (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (σ : ι → Bool) : 0 ≤ trialMass p σ := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact (hp i).1
  · exact sub_nonneg.mpr (hp i).2

lemma sum_trialMass (p : ι → ℝ) : ∑ σ : ι → Bool, trialMass p σ = 1 := by
  simp only [trialMass]
  rw [← Fintype.prod_sum (fun (i : ι) (b : Bool) => if b then p i else 1 - p i)]
  simp

lemma moment_eq (p a : ι → ℝ) :
    (∑ σ : ι → Bool, trialMass p σ *
      Real.exp (∑ i, if σ i then a i else 0)) =
        ∏ i, (1 - p i + p i * Real.exp (a i)) := by
  simp only [trialMass, Real.exp_sum, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : ι) (b : Bool) =>
    (if b then p i else 1 - p i) * Real.exp (if b then a i else 0))]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, Real.exp_zero, mul_one]
  ring

lemma moment_le (p a : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    (∑ σ : ι → Bool, trialMass p σ *
      Real.exp (∑ i, if σ i then a i else 0)) ≤
        Real.exp (∑ i, p i * (Real.exp (a i) - 1)) := by
  rw [moment_eq, Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro i _
    exact add_nonneg (sub_nonneg.mpr (hp i).2)
      (mul_nonneg (hp i).1 (Real.exp_pos _).le)
  · intro i _
    have h := Real.add_one_le_exp (p i * (Real.exp (a i) - 1))
    linarith

lemma subset_exponent (A : Finset ι) (σ : ι → Bool) (a : ℝ) :
    (∑ i, if σ i then (if i ∈ A then a else 0) else 0) = a * trialCount A σ := by
  rw [trialCount, Finset.mul_sum]
  rw [← Finset.sum_subset (Finset.subset_univ A)]
  · apply Finset.sum_congr rfl
    intro i hi
    simp only [hi, ↓reduceIte]
    split_ifs <;> simp
  · intro i _ hi
    simp [hi]

lemma subset_moment_le (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (A : Finset ι) (a : ℝ) :
    (∑ σ : ι → Bool, trialMass p σ * Real.exp (a * trialCount A σ)) ≤
      Real.exp ((Real.exp a - 1) * ∑ i ∈ A, p i) := by
  have h := moment_le p (fun i => if i ∈ A then a else 0) hp
  simp_rw [subset_exponent A] at h
  convert h using 1
  congr 1
  rw [Finset.mul_sum]
  rw [← Finset.sum_subset (Finset.subset_univ A)]
  · apply Finset.sum_congr rfl
    intro i hi
    simp [hi, mul_comm]
  · intro i _ hi
    simp [hi]

lemma shifted_subset_moment_le (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (A : Finset ι) (a b : ℝ) :
    (∑ σ : ι → Bool, trialMass p σ * Real.exp (a * trialCount A σ + b)) ≤
      Real.exp (b + (Real.exp a - 1) * ∑ i ∈ A, p i) := by
  calc
    _ = Real.exp b * ∑ σ : ι → Bool, trialMass p σ * Real.exp (a * trialCount A σ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      rw [Real.exp_add]
      ring
    _ ≤ Real.exp b * Real.exp ((Real.exp a - 1) * ∑ i ∈ A, p i) :=
      mul_le_mul_of_nonneg_left (subset_moment_le p hp A a) (Real.exp_pos b).le
    _ = _ := (Real.exp_add _ _).symm

lemma total_lower_tail_moment (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    (∑ σ : ι → Bool, trialMass p σ *
      Real.exp ((∑ i, p i) / 2 - trialCount Finset.univ σ)) ≤
        Real.exp (-(∑ i, p i) / 8) := by
  have hS : 0 ≤ ∑ i, p i := Finset.sum_nonneg fun i _ => (hp i).1
  have he : Real.exp (-1) ≤ (3 : ℝ) / 8 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos 1)).mpr
    nlinarith [Real.exp_one_gt_d9]
  have h := shifted_subset_moment_le p hp Finset.univ (-1) ((∑ i, p i) / 2)
  simp only [neg_one_mul, neg_add_eq_sub] at h
  exact h.trans (Real.exp_le_exp.mpr (by
    have hmul := mul_le_mul_of_nonneg_right he hS
    linarith))

lemma total_lower_tail_quarter (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hS : 8 * Real.log 4 ≤ ∑ i, p i) :
    (∑ σ : ι → Bool, trialMass p σ *
      Real.exp ((∑ i, p i) / 2 - trialCount Finset.univ σ)) ≤ (1 : ℝ) / 4 := by
  calc
    _ ≤ Real.exp (-(∑ i, p i) / 8) := total_lower_tail_moment p hp
    _ ≤ Real.exp (-Real.log 4) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

lemma test_shifted_moment (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (A : Finset ι) {μ c r : ℝ} (hc : 0 < c) (hμ : c ≤ μ) (hr : 0 ≤ r)
    (hmean : ∑ i ∈ A, p i ≤ μ) :
    (∑ σ : ι → Bool, trialMass p σ *
      Real.exp (trialCount A σ - (Real.exp 1 - 1 + r / c) * μ)) ≤
        Real.exp (-r) := by
  have h := shifted_subset_moment_le p hp A 1 (-(Real.exp 1 - 1 + r / c) * μ)
  simp only [one_mul, neg_mul, ← sub_eq_add_neg] at h
  have he : 0 ≤ Real.exp 1 - 1 := by linarith [Real.exp_one_gt_two]
  have hm := mul_le_mul_of_nonneg_left hmean he
  have hrc : r ≤ r / c * μ := by
    calc
      r = r / c * c := (div_mul_cancel₀ r hc.ne').symm
      _ ≤ r / c * μ := mul_le_mul_of_nonneg_left hμ (div_nonneg hr hc.le)
  exact h.trans (Real.exp_le_exp.mpr (by nlinarith))

lemma exists_trial_lt_one (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (f : (ι → Bool) → ℝ) (hf : (∑ σ : ι → Bool, trialMass p σ * f σ) < 1) :
    ∃ σ : ι → Bool, f σ < 1 := by
  by_contra h
  have hall : ∀ σ : ι → Bool, 1 ≤ f σ := by simpa only [not_exists, not_lt] using h
  have hbound : 1 ≤ ∑ σ : ι → Bool, trialMass p σ * f σ := by
    calc
      1 = ∑ σ : ι → Bool, trialMass p σ * 1 := by simp [sum_trialMass]
      _ ≤ _ := Finset.sum_le_sum fun σ _ =>
        mul_le_mul_of_nonneg_left (hall σ) (trialMass_nonneg p hp σ)
  exact (not_lt_of_ge hbound) hf

theorem finite_indexed_sample
    {β : Type*} [Fintype β]
    (p : ι → ℝ) (B : β → Finset ι) (μ : β → ℝ) (c : ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hc : 0 < c)
    (hμ : ∀ b, c ≤ μ b)
    (hmean : ∀ b, ∑ i ∈ B b, p i ≤ μ b)
    (hS : 8 * Real.log 4 ≤ ∑ i, p i) :
    ∃ s : Finset ι, (∑ i, p i) / 2 ≤ (s.card : ℝ) ∧
      ∀ b, ((s ∩ B b).card : ℝ) ≤
        (Real.exp 1 - 1 + Real.log (4 * ((Fintype.card β : ℝ) + 1)) / c) * μ b := by
  classical
  let r := Real.log (4 * ((Fintype.card β : ℝ) + 1))
  let L := Real.exp 1 - 1 + r / c
  let f := fun σ : ι → Bool =>
    Real.exp ((∑ i, p i) / 2 - trialCount Finset.univ σ) +
      ∑ b, Real.exp (trialCount (B b) σ - L * μ b)
  have hn : 0 ≤ (Fintype.card β : ℝ) := Nat.cast_nonneg _
  have hpos : 0 < 4 * ((Fintype.card β : ℝ) + 1) := by positivity
  have hr : 0 ≤ r := Real.log_nonneg (by linarith)
  have hbox (b : β) : (∑ σ : ι → Bool, trialMass p σ *
      Real.exp (trialCount (B b) σ - L * μ b)) ≤
        1 / (4 * ((Fintype.card β : ℝ) + 1)) := by
    calc
      _ ≤ Real.exp (-r) := test_shifted_moment p hp (B b) hc (hμ b) hr (hmean b)
      _ = _ := by dsimp [r]; rw [Real.exp_neg, Real.exp_log hpos, one_div]
  have hf : (∑ σ : ι → Bool, trialMass p σ * f σ) < 1 := by
    have hsplit : (∑ σ : ι → Bool, trialMass p σ * f σ) =
        (∑ σ : ι → Bool, trialMass p σ *
          Real.exp ((∑ i, p i) / 2 - trialCount Finset.univ σ)) +
        ∑ b, ∑ σ : ι → Bool, trialMass p σ *
          Real.exp (trialCount (B b) σ - L * μ b) := by
      dsimp [f]
      simp_rw [mul_add, Finset.mul_sum]
      rw [Finset.sum_add_distrib, Finset.sum_comm]
    rw [hsplit]
    have hboxes := Finset.sum_le_sum fun b (_ : b ∈ (Finset.univ : Finset β)) => hbox b
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hboxes
    have hnfrac : (Fintype.card β : ℝ) *
        (1 / (4 * ((Fintype.card β : ℝ) + 1))) < 1 / 4 := by
      rw [mul_one_div, div_lt_iff₀ hpos]
      linarith
    linarith [total_lower_tail_quarter p hp hS]
  obtain ⟨σ, hσ⟩ := exists_trial_lt_one p hp f hf
  have hlower : Real.exp ((∑ i, p i) / 2 - trialCount Finset.univ σ) < 1 := by
    have hnonneg : 0 ≤ ∑ b, Real.exp (trialCount (B b) σ - L * μ b) :=
      Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
    dsimp [f] at hσ
    linarith
  have htests (b : β) : Real.exp (trialCount (B b) σ - L * μ b) < 1 := by
    have hsingle := Finset.single_le_sum
      (fun b (_ : b ∈ (Finset.univ : Finset β)) => (Real.exp_pos
        (trialCount (B b) σ - L * μ b)).le) (Finset.mem_univ b)
    dsimp [f] at hσ
    linarith [Real.exp_pos ((∑ i, p i) / 2 - trialCount Finset.univ σ)]
  refine ⟨selected σ, ?_, ?_⟩
  · have := Real.exp_lt_one_iff.mp hlower
    rw [trialCount_eq_card, Finset.inter_univ] at this
    linarith
  · intro b
    have := Real.exp_lt_one_iff.mp (htests b)
    rw [trialCount_eq_card] at this
    exact le_of_lt (sub_neg.mp this)

noncomputable def logarithmicConstant (C d c : ℝ) : ℝ :=
  8 * Real.log 4 + Real.exp 1 + (Real.log (4 * (C + 1)) + d) / c

theorem logarithmic_indexed_sample
    {β : Type*} [Fintype β]
    (p : ι → ℝ) (B : β → Finset ι) (μ : β → ℝ)
    {C d c δ : ℝ} (hC : 1 ≤ C) (hd : 0 ≤ d) (hc : 0 < c)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hμ : ∀ b, c ≤ μ b)
    (hmean : ∀ b, ∑ i ∈ B b, p i ≤ μ b)
    (hcard : (Fintype.card β : ℝ) ≤ C * δ ^ (-d))
    (hS : logarithmicConstant C d c * (1 + Real.log (1 / δ)) ≤ ∑ i, p i) :
    0 < logarithmicConstant C d c ∧
    ∃ s : Finset ι, (∑ i, p i) / 2 ≤ (s.card : ℝ) ∧
      ∀ b, ((s ∩ B b).card : ℝ) ≤
        logarithmicConstant C d c * (1 + Real.log (1 / δ)) * μ b := by
  classical
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlogC : 0 ≤ Real.log (4 * (C + 1)) := Real.log_nonneg (by linarith)
  have hlogδ : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1.le
  have hl : 0 ≤ Real.log (1 / δ) := by rw [one_div, Real.log_inv]; linarith
  have hL : 0 < logarithmicConstant C d c := by
    dsimp [logarithmicConstant]
    positivity
  have hL8 : 8 * Real.log 4 ≤ logarithmicConstant C d c := by
    dsimp [logarithmicConstant]
    have hdiv := div_nonneg (add_nonneg hlogC hd) hc.le
    linarith [Real.exp_pos 1]
  have hS' : 8 * Real.log 4 ≤ ∑ i, p i := by
    have hm := mul_nonneg hL.le hl
    have : logarithmicConstant C d c ≤
        logarithmicConstant C d c * (1 + Real.log (1 / δ)) := by nlinarith
    exact hL8.trans (this.trans hS)
  have hpow : 1 ≤ δ ^ (-d) := by
    rw [Real.rpow_def_of_pos hδ]
    simpa only [Real.exp_zero] using
      Real.exp_le_exp.mpr (mul_nonneg_of_nonpos_of_nonpos hlogδ (neg_nonpos.mpr hd))
  have hnet : 4 * ((Fintype.card β : ℝ) + 1) ≤ 4 * (C + 1) * δ ^ (-d) := by
    nlinarith
  have hr : Real.log (4 * ((Fintype.card β : ℝ) + 1)) ≤
      Real.log (4 * (C + 1)) + d * Real.log (1 / δ) := by
    have hh := Real.log_le_log (by positivity : 0 < 4 * ((Fintype.card β : ℝ) + 1)) hnet
    rw [Real.log_mul (by positivity : 4 * (C + 1) ≠ 0)
      (ne_of_gt (Real.rpow_pos_of_pos hδ (-d))), Real.log_rpow hδ] at hh
    rw [one_div, Real.log_inv]
    nlinarith
  have hcoeff : Real.exp 1 - 1 +
      Real.log (4 * ((Fintype.card β : ℝ) + 1)) / c ≤
        logarithmicConstant C d c * (1 + Real.log (1 / δ)) := by
    have hdivide := div_le_div_of_nonneg_right hr hc.le
    have hfirst : Real.exp 1 - 1 + Real.log (4 * (C + 1)) / c ≤
        logarithmicConstant C d c := by
      dsimp [logarithmicConstant]
      rw [add_div]
      linarith [div_nonneg hd hc.le]
    have hsecond : d / c ≤ logarithmicConstant C d c := by
      dsimp [logarithmicConstant]
      rw [add_div]
      linarith [Real.exp_pos 1, div_nonneg hlogC hc.le]
    have hmul := mul_le_mul_of_nonneg_right hsecond hl
    rw [add_div] at hdivide
    rw [mul_div_right_comm] at hdivide
    nlinarith
  obtain ⟨s, hs, htests⟩ := finite_indexed_sample p B μ c hp hc hμ hmean hS'
  refine ⟨hL, s, hs, fun b => (htests b).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hcoeff (hc.le.trans (hμ b))

end Kakeya.WeightedConvex

end OAI
