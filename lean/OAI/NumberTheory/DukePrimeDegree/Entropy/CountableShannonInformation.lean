import OAI.NumberTheory.DukePrimeDegree.Entropy.ObservationInformation

namespace OAI

/-! # Integrable information for the countable return observations

The summable atom estimates for return refinements give the actual
integrable information function, and bound every finite recoding.
-/

noncomputable section
open MeasureTheory Set Function
namespace DukePrimeDegree
open PrimeDegreePackets

lemma integrableOn_observationInformation_fiber
    {Y α : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a}) (a : α) :
    IntegrableOn (observationInformation μ P) {y | P y=a} μ := by
  apply (integrable_const (-Real.log (μ.real {y | P y=a}))).congr
  filter_upwards [ae_restrict_mem (hP a)] with y hy
  simp only [observationInformation,hy]

lemma setIntegral_observationInformation_fiber
    {Y α : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a}) (a : α) :
    (∫ y in {y | P y=a}, observationInformation μ P y ∂μ) =
      Real.negMulLog (μ.real {y | P y=a}) := by
  calc
    _ = ∫ _ in {y | P y=a}, -Real.log (μ.real {y | P y=a}) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (hP a)] with y hy
      simp only [observationInformation,hy]
    _ = _ := by simp [Real.negMulLog_def,Measure.real,neg_mul,mul_neg]

/-- Summable Shannon terms are sufficient for integrability of the
countable partition's pointwise information. -/
theorem countable_observationInformation_integrable
    {Y α : Type*} [MeasurableSpace Y] [Countable α]
    (μ : Measure Y) [IsProbabilityMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a})
    (hs : Summable (fun a => Real.negMulLog (μ.real {y | P y=a}))) :
    Integrable (observationInformation μ P) μ := by
  have hnorm (a : α) :
      (∫ y in {y | P y=a}, ‖observationInformation μ P y‖ ∂μ) =
        Real.negMulLog (μ.real {y | P y=a}) := by
    simp_rw [Real.norm_eq_abs,abs_of_nonneg (observationInformation_nonneg μ P _)]
    exact setIntegral_observationInformation_fiber μ P hP a
  have H := integrableOn_iUnion_of_summable_integral_norm
    (fun a => integrableOn_observationInformation_fiber μ P hP a)
    (by simpa only [hnorm] using hs)
  have he : (⋃ a, {y | P y=a})=univ := by ext y; simp
  rwa [he,integrableOn_univ] at H

theorem integral_countable_observationInformation
    {Y α : Type*} [MeasurableSpace Y] [Countable α]
    (μ : Measure Y) [IsProbabilityMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a})
    (hs : Summable (fun a => Real.negMulLog (μ.real {y | P y=a}))) :
    (∫ y, observationInformation μ P y ∂μ) =
      ∑' a, Real.negMulLog (μ.real {y | P y=a}) := by
  have he : (⋃ a, {y | P y=a})=univ := by ext y; simp
  have hd : Pairwise (Disjoint on (fun a => {y | P y=a})) := by
    intro a b hab
    change Disjoint {y | P y=a} {y | P y=b}
    rw [Set.disjoint_left]
    intro y ha hb
    exact hab (ha.symm.trans hb)
  have H := integral_iUnion hP hd
    ((countable_observationInformation_integrable μ P hP hs).integrableOn)
  simpa only [he,Measure.restrict_univ,setIntegral_observationInformation_fiber μ P hP] using H

lemma ae_observation_fiber_pos
    {Y α : Type*} [MeasurableSpace Y] [Countable α]
    (μ : Measure Y) (P : Y → α) :
    ∀ᵐ y ∂μ, 0 < μ {z | P z=P y} := by
  have h (a : α) : ∀ᵐ y ∂μ, P y=a → 0 < μ {z | P z=a} := by
    by_cases ha : μ {z | P z=a}=0
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp ha] with y hy
      exact fun hya => (hy hya).elim
    · exact ae_of_all _ (fun _ _ => pos_iff_ne_zero.mpr ha)
  filter_upwards [ae_all_iff.mpr h] with y hy
  exact hy (P y) rfl

/-- Every finite recoding is bounded by the same countable Shannon sum. -/
theorem finite_recode_entropy_le_countable_information
    {Y α β : Type*} [MeasurableSpace Y] [Countable α] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a})
    (hs : Summable (fun a => Real.negMulLog (μ.real {y | P y=a})))
    (f : α → β) (hf : ∀ b, MeasurableSet {y | f (P y)=b}) :
    observationEntropy μ (f ∘ P) ≤ ∑' a, Real.negMulLog (μ.real {y | P y=a}) := by
  rw [←integral_countable_observationInformation μ P hP hs,
    ←integral_observationInformation μ (f ∘ P) hf]
  apply integral_mono_ae (observationInformation_integrable μ (f ∘ P) hf)
    (countable_observationInformation_integrable μ P hP hs)
  filter_upwards [ae_observation_fiber_pos μ P] with y hy
  apply neg_le_neg
  apply Real.log_le_log (ENNReal.toReal_pos hy.ne' (measure_ne_top μ _))
  exact measureReal_mono (μ := μ) (fun z hz => congrArg f hz) (measure_ne_top μ _)

end DukePrimeDegree

end

end OAI
