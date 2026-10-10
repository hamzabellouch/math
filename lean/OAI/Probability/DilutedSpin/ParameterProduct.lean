import Mathlib

namespace OAI

section
section
namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

/-- Refreshing a single coordinate by an independent sample preserves the
entire countable parameter law. The other coordinates are not truncated. -/
theorem measurePreserving_parameter_refresh {ι : Type*} [DecidableEq ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    MeasurePreserving (fun z : (ι → ℝ) × ℝ => Function.update z.1 i z.2)
      ((Measure.infinitePi μ).prod (μ i)) (Measure.infinitePi μ) := by
  have hm : Measurable (fun z : (ι → ℝ) × ℝ => Function.update z.1 i z.2) := by
    apply Measurable.of_eval
    intro j
    by_cases h : j = i
    · subst j
      simpa using (measurable_snd : Measurable (fun z : (ι → ℝ) × ℝ => z.2))
    · simp only [Function.update_of_ne h]
      fun_prop
  refine ⟨hm,Measure.eq_infinitePi μ ?_⟩
  intro s t ht
  rw [Measure.map_apply hm (MeasurableSet.pi s.countable_toSet (fun j _ => ht j))]
  have he : (fun z : (ι → ℝ) × ℝ => Function.update z.1 i z.2) ⁻¹' ((s : Set ι).pi t) =
      ((s.erase i : Set ι).pi t) ×ˢ (if i ∈ s then t i else Set.univ) := by
    ext z
    simp only [mem_preimage,mem_prod,mem_pi,Finset.mem_coe,Finset.mem_erase]
    constructor
    · intro hz
      constructor
      · intro j hj
        simpa [Function.update_of_ne hj.1] using hz j hj.2
      · split_ifs with hi
        · simpa using hz i hi
        · trivial
    · rintro ⟨hz,hi⟩ j hj
      by_cases h : j = i
      · subst j
        simpa [hj] using hi
      · simpa [Function.update_of_ne h] using hz j ⟨h,hj⟩
  rw [he,Measure.prod_prod,Measure.infinitePi_pi μ (fun j _ => ht j)]
  by_cases hi : i ∈ s
  · rw [ite_eq_left hi]
    exact Finset.prod_erase_mul _ _ hi
  · simp [hi]

end DilutedSpinGlass

namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

 
noncomputable def intervalParameterLaw (a b : ℝ) : Measure ℝ := volume[|Icc a b]

lemma intervalParameterLaw_probability {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (intervalParameterLaw a b) := by
  apply cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

lemma integral_intervalParameterLaw {a b : ℝ} (hab : a < b) (f : ℝ → ℝ) :
    (∫ u, f u ∂intervalParameterLaw a b) = (∫ u in a..b, f u)/(b-a) := by
  rw [intervalParameterLaw,ProbabilityTheory.cond,integral_smul_measure,Real.volume_Icc,
    ENNReal.toReal_inv,ENNReal.toReal_ofReal (sub_pos.mpr hab).le,
    integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab.le]
  simp only [smul_eq_mul,div_eq_mul_inv,mul_comm]

/-- A complete-parameter average is the independent refresh average. -/
lemma integral_parameter_refresh {ι : Type*} [DecidableEq ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (i : ι)
    (f : (ι → ℝ) → ℝ) (hf : Measurable f) (hi : Integrable f (Measure.infinitePi μ)) :
    (∫ z, f z ∂Measure.infinitePi μ) =
      ∫ z, ∫ u, f (Function.update z i u) ∂μ i ∂Measure.infinitePi μ := by
  let H := measurePreserving_parameter_refresh μ i
  have hcomp : Integrable (fun z : (ι → ℝ) × ℝ => f (Function.update z.1 i z.2))
      ((Measure.infinitePi μ).prod (μ i)) :=
    (H.integrable_comp hf.aestronglyMeasurable).mpr hi
  rw [← integral_prod _ hcomp]
  calc
    _ = ∫ y, f y ∂Measure.map (fun z : (ι → ℝ) × ℝ => Function.update z.1 i z.2)
        ((Measure.infinitePi μ).prod (μ i)) := by rw [H.map_eq]
    _ = _ := integral_map H.measurable.aemeasurable hf.aestronglyMeasurable

/-- Uniform interval estimates with every other coordinate fixed imply the
same estimate under the literal infinite product parameter law. -/
lemma parameter_average_le {ι : Type*} [DecidableEq ι]
    (a b : ι → ℝ) (hab : ∀ i, a i < b i) (i : ι)
    (f : (ι → ℝ) → ℝ) (hf : Measurable f)
    (hi : Integrable f (Measure.infinitePi (fun i => intervalParameterLaw (a i) (b i))))
    {B : ℝ} (hB : ∀ z, (∫ u in a i..b i, f (Function.update z i u))/(b i-a i) ≤ B) :
    (∫ z, f z ∂Measure.infinitePi (fun i => intervalParameterLaw (a i) (b i))) ≤ B := by
  let μ := fun i => intervalParameterLaw (a i) (b i)
  let (i : ι) : IsProbabilityMeasure (μ i) := intervalParameterLaw_probability (hab i)
  rw [integral_parameter_refresh μ i f hf hi]
  have hcomp := ((measurePreserving_parameter_refresh μ i).integrable_comp
    hf.aestronglyMeasurable).mpr hi
  have hm := integral_mono hcomp.integral_prod_left (integrable_const B) (fun z => by
    simpa only [μ,integral_intervalParameterLaw (hab i),Function.comp_apply] using hB z)
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul,Function.comp_apply] using hm

end DilutedSpinGlass
end

end

section
section
namespace DilutedSpinGlass
open MeasureTheory

/-- Selecting one type in the complete dictionary law keeps its unmodified
conditional site law. This is the scalar normalization in the Palm identity. -/
lemma integral_select_product {J Z : Type*} [MeasurableSpace J] [MeasurableSingletonClass J]
    [MeasurableSpace Z] [Countable J] [Countable Z] [MeasurableSingletonClass Z]
    [DecidableEq J] (ν : Measure J) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (j : J) (F : J × Z → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B) :
    (∫ x, if x.1 = j then F x else 0 ∂ν.prod τ) =
      ν.real {j} * ∫ z, F (j,z) ∂τ := by
  have hm : Measurable (fun x : J × Z => if x.1 = j then F x else 0) := measurable_of_countable _
  have hi : Integrable (fun x : J × Z => if x.1 = j then F x else 0) (ν.prod τ) := by
    apply Integrable.of_bound hm.aestronglyMeasurable B
    exact ae_of_all _ (fun x => by rw [Real.norm_eq_abs]; split_ifs; exact hF x; simpa using hB)
  rw [integral_prod _ hi]
  have he : (fun x : J => ∫ z, if x = j then F (x,z) else 0 ∂τ) =
      Set.indicator {j} (fun x => ∫ z, F (x,z) ∂τ) := by
    funext x
    by_cases hx : x = j
    · simp [hx]
    · simp [hx]
  rw [he,integral_indicator (measurableSet_singleton j),integral_singleton]
  rfl

/-- Inserting with a pushed-forward site law is genuinely independent of the
old reservoir. The old state law is not changed by this relabeling. -/
lemma integral_fresh_label {W J Z : Type*} [MeasurableSpace W] [MeasurableSpace J]
    [MeasurableSpace Z] (ρ : Measure W) [IsProbabilityMeasure ρ]
    (τ : Measure Z) [IsProbabilityMeasure τ] (label : Z → J) (hl : Measurable label)
    (F : W × J → ℝ) (hF : Measurable F) {B : ℝ} (hb : ∀ z, |F z| ≤ B) :
    (∫ z, F z ∂ρ.prod (τ.map label)) = ∫ w, ∫ z, F (w,label z) ∂τ ∂ρ := by
  have hi : Integrable F (ρ.prod (τ.map label)) :=
    Integrable.of_bound hF.aestronglyMeasurable B (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hb z))
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun w => integral_map hl.aemeasurable (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)

end DilutedSpinGlass
end

end

end OAI
