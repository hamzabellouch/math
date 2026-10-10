import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.PredictableVersion

theorem exists_stronglyMeasurable_version_of_ae_tendsto
    {A : Type*} [mA : MeasurableSpace A] (m : MeasurableSpace A)
    (μ : Measure[mA] A) {f : ℕ → A → ℝ} {g : A → ℝ}
    (hf : ∀ n, StronglyMeasurable[m] (f n))
    (hfg : ∀ᵐ a ∂μ, Tendsto (fun n => f n a) atTop (𝓝 (g a))) :
    ∃ v : A → ℝ, StronglyMeasurable[m] v ∧ v =ᵐ[μ] g := by
  refine ⟨fun a => limsup (fun n => f n a) atTop, ?_, ?_⟩
  · exact (Measurable.limsup (fun n => (hf n).measurable)).stronglyMeasurable
  · filter_upwards [hfg] with a ha
    exact ha.limsup_eq

theorem exists_stronglyMeasurable_version_of_tendstoInMeasure
    {A : Type*} [mA : MeasurableSpace A] (m : MeasurableSpace A)
    (μ : Measure[mA] A) {f : ℕ → A → ℝ} {g : A → ℝ}
    (hf : ∀ n, StronglyMeasurable[m] (f n))
    (hfg : TendstoInMeasure μ f atTop g) :
    ∃ v : A → ℝ, StronglyMeasurable[m] v ∧ v =ᵐ[μ] g := by
  obtain ⟨ns, _, hns⟩ := hfg.exists_seq_tendsto_ae
  exact exists_stronglyMeasurable_version_of_ae_tendsto (mA := mA) m μ (fun n => hf (ns n)) hns

theorem predictable_le_product {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) :
    F.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    exact (measurableSet_singleton (0 : ℝ≥0)).prod (F.le 0 A hA)
  · intro t A hA
    exact measurableSet_Ioi.prod (F.le t A hA)

theorem exists_predictable_version_of_tendstoInMeasure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (F : Filtration ℝ≥0 mΩ)
    (μ : Measure (ℝ≥0 × Ω)) {f : ℕ → ℝ≥0 → Ω → ℝ} {g : ℝ≥0 → Ω → ℝ}
    (hf : ∀ n, IsStronglyPredictable F (f n))
    (hfg : TendstoInMeasure μ (fun n => Function.uncurry (f n)) atTop
      (Function.uncurry g)) :
    ∃ v : ℝ≥0 → Ω → ℝ, IsStronglyPredictable F v ∧
      Function.uncurry v =ᵐ[μ] Function.uncurry g := by
  obtain ⟨v, hv, heq⟩ := exists_stronglyMeasurable_version_of_tendstoInMeasure
    F.predictable μ hf hfg
  exact ⟨Function.curry v, hv, heq⟩

theorem exists_predictable_version_of_tendsto_eLpNorm
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (F : Filtration ℝ≥0 mΩ)
    (μ : Measure (ℝ≥0 × Ω)) {f : ℕ → ℝ≥0 → Ω → ℝ} {g : ℝ≥0 → Ω → ℝ}
    (hf : ∀ n, IsStronglyPredictable F (f n))
    (hg : MemLp (Function.uncurry g) 2 μ)
    (hfg : Tendsto (fun n => eLpNorm
      (Function.uncurry (f n) - Function.uncurry g) 2 μ) atTop (𝓝 0)) :
    ∃ v : ℝ≥0 → Ω → ℝ, IsStronglyPredictable F v ∧
      MemLp (Function.uncurry v) 2 μ ∧
      Function.uncurry v =ᵐ[μ] Function.uncurry g := by
  obtain ⟨v, hv, heq⟩ := exists_predictable_version_of_tendstoInMeasure F μ hf
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hfg)
  exact ⟨v, hv, hg.ae_eq heq.symm, heq⟩

end Problem367.PredictableVersion

end

end OAI
