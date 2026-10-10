import OAI.Analysis.IrrationalRotation.Model.ProductIdealSampling
import OAI.Analysis.IrrationalRotation.Sampling.ProductSampling
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingTrimming
import OAI.Analysis.IrrationalRotation.Analysis.VaryingMapWeakLimit

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace Invariant233.ProductModel.IdealSampling

instance sourceMeasure_finite (I : Finset ℕ) : IsFiniteMeasure (sourceMeasure I) := by
  unfold sourceMeasure
  infer_instance

instance uncutLaw_finite (I D : Finset ℕ) (h : ℝ) : IsFiniteMeasure (uncutLaw I D h) := by
  unfold uncutLaw
  infer_instance

instance law_finite (I D : Finset ℕ) (h α : ℝ) : IsFiniteMeasure (law I D h α) := by
  unfold law
  infer_instance

@[fun_prop]
theorem endpointMap_measurable (I D : Finset ℕ) (h : ℝ) :
    Measurable (endpointMap I D h) := by
  apply measurable_fst.prodMk
  apply Measurable.of_eval
  intro i
  by_cases hi : i ∈ I
  · simpa [endpoint, endpointMap, hi, Function.comp_def] using
      (measurable_pi_apply i).comp measurable_snd
  · by_cases hd : i ∈ D
    · simp only [endpoint, hi, hd, ite_false, ite_true]
      have hx : Measurable (fun xz : EndpointPair => circleRepresentative (xz.1 i)) := by
        fun_prop
      have hz : Measurable (fun xz : EndpointPair => circleRepresentative (xz.2 i)) := by
        fun_prop
      have hδ : Measurable (fun xz : EndpointPair =>
          ScalarSampling.delta (circleRepresentative (xz.1 i))) :=
        hx.min (measurable_const.sub hx)
      have hc : Continuous (fun r : ℝ => (r : Circle)) := by fun_prop
      exact ((measurable_pi_apply i).comp measurable_fst).add
        (hc.measurable.comp ((measurable_const.mul hδ).mul hz))
    · simpa [endpoint, endpointMap, hi, hd, Function.comp_def] using
        (measurable_pi_apply i).comp measurable_fst

theorem cutoffEvent_measurable (I D : Finset ℕ) (α : ℝ) :
    MeasurableSet (cutoffEvent I D α) := by
  unfold cutoffEvent
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _
  have hx : Measurable (fun xz : EndpointPair => circleRepresentative (xz.1 i)) := by
    fun_prop
  exact measurableSet_le measurable_const (hx.min (measurable_const.sub hx))

theorem endpointMap_tendsto (I : Finset ℕ) (D : ℕ → Finset ℕ)
    {h : ℕ → ℝ} (hh : Tendsto h atTop (𝓝 0)) (xz : EndpointPair) :
    Tendsto (fun l => endpointMap I (D l) (h l) xz) atTop
      (𝓝 (xz.1, selectedEndpoint I xz.1 xz.2)) := by
  apply tendsto_const_nhds.prodMk_nhds
  apply tendsto_pi_nhds.mpr
  intro i
  by_cases hi : i ∈ I
  · simp [endpoint, selectedEndpoint, hi]
  · have hr : Tendsto (fun l => h l * ScalarSampling.delta
        (circleRepresentative (xz.1 i)) * circleRepresentative (xz.2 i))
        atTop (𝓝 0) := by
      simpa using (hh.mul_const (ScalarSampling.delta
        (circleRepresentative (xz.1 i)))).mul_const (circleRepresentative (xz.2 i))
    have hc : Continuous (fun r : ℝ => (r : Circle)) := by fun_prop
    have ha : Tendsto (fun l => xz.1 i + ((h l * ScalarSampling.delta
        (circleRepresentative (xz.1 i)) * circleRepresentative (xz.2 i) : ℝ) : Circle))
        atTop (𝓝 (xz.1 i)) := by
      simpa using tendsto_const_nhds.add (hc.continuousAt.tendsto.comp hr)
    simpa [endpoint, selectedEndpoint, hi] using
      (ha.if' (p := fun l => i ∈ D l) tendsto_const_nhds)

theorem uncutLaw_weaklyConverges (I : Finset ℕ) (D : ℕ → Finset ℕ)
    {h : ℕ → ℝ} (hh : Tendsto h atTop (𝓝 0)) :
    WeaklyConverges (fun l => uncutLaw I (D l) (h l)) (triangularLaw I) := by
  let μ : FiniteMeasure EndpointPair := ⟨sourceMeasure I, inferInstance⟩
  have hv := VaryingMapWeakLimit.tendsto_map_of_ae_tendsto μ
    (fun l => endpointMap I (D l) (h l))
    (fun xz : EndpointPair => (xz.1, selectedEndpoint I xz.1 xz.2))
    (fun l => endpointMap_measurable I (D l) (h l))
    (Sampling.endpointMap_measurable I)
    (Filter.Eventually.of_forall (endpointMap_tendsto I D hh))
  exact (weaklyConverges_iff_tendsto _ _).mpr hv

theorem circle_cutoff_loss_le {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    circleMeasure {x : Circle | ScalarSampling.delta (circleRepresentative x) < α} ≤
      ENNReal.ofReal (2 * α) := by
  have heq : {x : Circle | ScalarSampling.delta (circleRepresentative x) < α} =
      {x | circleRepresentative x < α} ∪
        {x | 1 - α < circleRepresentative x} := by
    ext x
    simp only [mem_ofPred_eq, mem_union, ScalarSampling.delta, min_lt_iff]
    constructor <;> intro hx
    · rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (by linarith)
    · rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (by linarith)
  rw [heq]
  calc
    _ ≤ circleMeasure {x | circleRepresentative x < α} +
        circleMeasure {x | 1 - α < circleRepresentative x} := measure_union_le _ _
    _ = ENNReal.ofReal α + ENNReal.ofReal α := by
      rw [Sampling.representative_initial_measure hα0 hα1,
        Sampling.representative_tail_measure (by linarith : 0 ≤ 1 - α)
          (by linarith : 1 - α ≤ 1)]
      congr 1
      congr 1
      ring

    _ = ENNReal.ofReal (2 * α) := by rw [← ENNReal.ofReal_add hα0 hα0]; congr 1; ring

theorem cutoff_loss_le (I D : Finset ℕ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    sourceMeasure I (cutoffEvent I D α)ᶜ ≤
      ENNReal.ofReal (2 * ((D \ I).card : ℝ) * α) := by
  let B : Set Circle := {x | ScalarSampling.delta (circleRepresentative x) < α}
  have hB : MeasurableSet B := measurableSet_lt
    (Sampling.representative_measurable.min
      (measurable_const.sub Sampling.representative_measurable)) measurable_const
  let bad : ℕ → Set EndpointPair := fun i => {xz | xz.1 i ∈ B}
  have hbad (i : ℕ) : (baseMeasure.prod baseMeasure) (bad i) ≤ ENNReal.ofReal (2 * α) := by
    have he : MeasurePreserving (fun x : Base => x i) baseMeasure circleMeasure :=
      measurePreserving_eval_infinitePi (fun _ : ℕ => circleMeasure) i
    have hf : MeasurePreserving (fun xz : EndpointPair => xz.1 i)
        (baseMeasure.prod baseMeasure) circleMeasure := he.comp measurePreserving_fst
    have hm := hf.measure_preimage hB.nullMeasurableSet
    change (baseMeasure.prod baseMeasure) ((fun xz : EndpointPair => xz.1 i) ⁻¹' B) ≤ _
    rw [hm]
    exact circle_cutoff_loss_le hα0 hα1
  have heq : (cutoffEvent I D α)ᶜ = ⋃ i ∈ D \ I, bad i := by
    ext xz
    simp [cutoffEvent, bad, B, and_assoc]
  calc
    sourceMeasure I (cutoffEvent I D α)ᶜ ≤
        (baseMeasure.prod baseMeasure) (cutoffEvent I D α)ᶜ := Measure.restrict_le_self _
    _ = (baseMeasure.prod baseMeasure) (⋃ i ∈ D \ I, bad i) := by rw [heq]
    _ ≤ ∑ i ∈ D \ I, (baseMeasure.prod baseMeasure) (bad i) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ D \ I, ENNReal.ofReal (2 * α) := Finset.sum_le_sum (fun i _ => hbad i)
    _ = ENNReal.ofReal (2 * ((D \ I).card : ℝ) * α) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      ring

theorem cutoff_loss_tendsto_zero (I : Finset ℕ) (D : ℕ → Finset ℕ)
    {α : ℕ → ℝ} (hα0 : ∀ l, 0 ≤ α l) (hα1 : ∀ l, α l ≤ 1)
    (hcut : Tendsto (fun l => ((D l \ I).card : ℝ) * α l) atTop (𝓝 0)) :
    Tendsto (fun l => sourceMeasure I (cutoffEvent I (D l) (α l))ᶜ) atTop (𝓝 0) := by
  have hb : Tendsto (fun l => ENNReal.ofReal
      (2 * ((D l \ I).card : ℝ) * α l)) atTop (𝓝 0) := by
    have hr := hcut.const_mul 2
    have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero, mul_assoc] using he
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
  · intro l
    exact bot_le
  · intro l
    exact cutoff_loss_le I (D l) (hα0 l) (hα1 l)

theorem law_weaklyConverges (I : Finset ℕ) (D : ℕ → Finset ℕ)
    {h α : ℕ → ℝ} (hh : Tendsto h atTop (𝓝 0))
    (hα0 : ∀ l, 0 ≤ α l) (hα1 : ∀ l, α l ≤ 1)
    (hcut : Tendsto (fun l => ((D l \ I).card : ℝ) * α l) atTop (𝓝 0)) :
    WeaklyConverges (fun l => law I (D l) (h l) (α l)) (triangularLaw I) := by
  let μ : FiniteMeasure EndpointPair := ⟨sourceMeasure I, inferInstance⟩
  have hlost := cutoff_loss_tendsto_zero I D hα0 hα1 hcut
  have hlost' : Tendsto (fun l => μ (cutoffEvent I (D l) (α l))ᶜ) atTop (𝓝 0) := by
    change Tendsto (fun l => (sourceMeasure I (cutoffEvent I (D l) (α l))ᶜ).toNNReal)
      atTop (𝓝 0)
    exact (ENNReal.tendsto_toNNReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hlost
  have hv := VaryingMapWeakLimit.tendsto_map_restrict_of_ae_tendsto μ
    (fun l => endpointMap I (D l) (h l))
    (fun xz : EndpointPair => (xz.1, selectedEndpoint I xz.1 xz.2))
    (fun l => endpointMap_measurable I (D l) (h l))
    (Sampling.endpointMap_measurable I)
    (Filter.Eventually.of_forall (endpointMap_tendsto I D hh))
    (fun l => cutoffEvent I (D l) (α l))
    (fun l => cutoffEvent_measurable I (D l) (α l)) hlost'
  exact (weaklyConverges_iff_tendsto _ _).mpr hv

theorem law_weaklyConverges_of_linear_dimension
    (I : Finset ℕ) (D : ℕ → Finset ℕ) (m : ℕ → ℕ)
    (hm : ∀ l, 1 ≤ m l) (hmTop : Tendsto m atTop atTop)
    {C : ℝ}
    (hD : ∀ l, ((D l).card : ℝ) ≤ C * (m l : ℝ)) :
    WeaklyConverges (fun l => law I (D l)
      ((m l : ℝ) ^ (-(3 / 5 : ℝ))) (1 / (m l : ℝ) ^ 2)) (triangularLaw I) := by
  have hmR : Tendsto (fun l => (m l : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hmTop
  have hm1 (l : ℕ) : (1 : ℝ) ≤ m l := by exact_mod_cast hm l
  have hmp (l : ℕ) : (0 : ℝ) < m l := lt_of_lt_of_le zero_lt_one (hm1 l)
  apply law_weaklyConverges I D
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 5)).comp hmR)
  · intro l
    positivity
  · intro l
    apply (div_le_one (sq_pos_of_pos (hmp l))).mpr
    nlinarith [hm1 l]
  · have hi : Tendsto (fun l => C * (m l : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp hmR).const_mul C
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hi
    · intro l
      positivity
    · intro l
      have hc : ((D l \ I).card : ℝ) ≤ C * (m l : ℝ) :=
        (Nat.cast_le.mpr (Finset.card_le_card Finset.sdiff_subset)).trans (hD l)
      calc
        ((D l \ I).card : ℝ) * (1 / (m l : ℝ) ^ 2) ≤
            (C * (m l : ℝ)) * (1 / (m l : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
        _ = C * (m l : ℝ)⁻¹ := by field_simp

end Invariant233.ProductModel.IdealSampling

end

end OAI
