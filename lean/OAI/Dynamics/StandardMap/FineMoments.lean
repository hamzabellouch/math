import OAI.Dynamics.StandardMap.TerminalCap

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace StandardMapEntropy
lemma shortfall_translate (d:DistanceArray) (s t r:DyadicTime) :
    arrayShortfall s t (arrayTranslate r d)=arrayShortfall (s+r) (t+r) d := by
  unfold arrayShortfall
  change 1-d.val (s+r) (t+r)/((t:ℝ)-(s:ℝ))=1-d.val (s+r) (t+r)/(((t:ℝ)+(r:ℝ))-((s:ℝ)+(r:ℝ)))
  rw [add_sub_add_right_eq_sub]
lemma shortfall_dilate (d:DistanceArray) (s t:DyadicTime) :
    arrayShortfall s t (arrayDilate d)=arrayShortfall (s+s) (t+t) d := by
  unfold arrayShortfall
  change 1-(d.val (s+s) (t+t)/2)/((t:ℝ)-(s:ℝ))=1-d.val (s+s) (t+t)/(((t:ℝ)+(t:ℝ))-((s:ℝ)+(s:ℝ)))
  congr 1
  rw [div_div]
  congr 1
  ring
lemma capG_coboundary (α:ℝ) (d:DistanceArray) :
    capG α d=capF α (arrayDilate d)-(capF α d+capF α (arrayTranslate (dyadicInt 1) d))/2 := by
  unfold capG capF
  rw [shortfall_dilate,shortfall_translate,zero_add,zero_add]
  have h2 : dyadicInt 1+dyadicInt 1=dyadicInt 2 := by apply Subtype.ext; norm_num
  rw [h2]
lemma integral_invariant_translation (μ:Measure NonAffineArray) (r:DyadicTime)
    (ht:μ.map (nonaffineTranslation r)=μ) (f:NonAffineArray→ℝ) (hf:Measurable f) :
    (∫d,f (nonaffineTranslation r d) ∂μ)=∫d,f d ∂μ := by
  rw [←integral_map (nonaffineTranslation r).continuous.measurable.aemeasurable hf.aestronglyMeasurable,ht]
lemma half_shortfall_average (d:NonAffineArray) (hu:UnitArray d.val) :
    (arrayShortfall 0 (dyadicInt 1) (nonaffineHalf d).val+
      arrayShortfall 0 (dyadicInt 1) (nonaffineHalf (nonaffineTranslation (dyadicHalf (dyadicInt 1)) d)).val)/2≤arrayShortfall 0 (dyadicInt 1) d.val := by
  have hj := arrayJ_nonneg 0 (dyadicInt 2) (by norm_num) (nonaffineHalf d).val
  have hs : arrayShortfall 0 (dyadicInt 2) (nonaffineHalf d).val=arrayShortfall 0 (dyadicInt 1) d.val := by
    have he := shortfall_dilate (nonaffineHalf d).val 0 (dyadicInt 1)
    rw [show (0:DyadicTime)+0=0 by simp,show dyadicInt 1+dyadicInt 1=dyadicInt 2 by apply Subtype.ext; norm_num] at he
    rw [show arrayDilate (nonaffineHalf d).val=d.val from congrArg Subtype.val (nonaffineDilate_half d hu)] at he
    exact he.symm
  have ht : arrayShortfall (dyadicInt 1) (dyadicInt 2) (nonaffineHalf d).val=
      arrayShortfall 0 (dyadicInt 1) (nonaffineHalf (nonaffineTranslation (dyadicHalf (dyadicInt 1)) d)).val := by
    rw [←half_translate (dyadicInt 1) d hu]
    change _=arrayShortfall 0 (dyadicInt 1) (arrayTranslate (dyadicInt 1) (nonaffineHalf d).val)
    rw [shortfall_translate,zero_add,show dyadicInt 1+dyadicInt 1=dyadicInt 2 by apply Subtype.ext; norm_num]
  simp only [arrayJ,dyadicMid_zero_two,hs,ht] at hj
  linarith
lemma shortfall_half_moment (μ:Measure NonAffineArray) (hu:∀ᵐd ∂μ,UnitArray d.val)
    (ht:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ)
    (hi:Integrable (fun d:NonAffineArray => arrayShortfall 0 (dyadicInt 1) d.val) μ) :
    Integrable (fun d:NonAffineArray => arrayShortfall 0 (dyadicInt 1) d.val) (μ.map nonaffineHalf) ∧
      (∫d:NonAffineArray,arrayShortfall 0 (dyadicInt 1) d.val ∂μ.map nonaffineHalf)≤
        ∫d:NonAffineArray,arrayShortfall 0 (dyadicInt 1) d.val ∂μ := by
  let f:NonAffineArray→ℝ := fun d => arrayShortfall 0 (dyadicInt 1) d.val
  have hf:Measurable f := (continuous_arrayShortfall _ _).measurable.comp measurable_subtype_coe
  have hb : Integrable (fun d => f (nonaffineHalf d)) μ := (hi.const_mul 2).mono'
    (hf.comp measurable_nonaffineHalf).aestronglyMeasurable (by
      filter_upwards [hu] with d hd
      rw [Real.norm_eq_abs,abs_of_nonneg (shortfall_unit_mem _ (nonaffineHalf_unit d hd) _ _ (by norm_num)).1]
      exact shortfall_half_bound d hd)
  refine ⟨(integrable_map_measure hf.aestronglyMeasurable measurable_nonaffineHalf.aemeasurable).mpr hb,?_⟩
  rw [integral_map measurable_nonaffineHalf.aemeasurable hf.aestronglyMeasurable]
  have hbt : Integrable (fun d => f (nonaffineHalf (nonaffineTranslation (dyadicHalf (dyadicInt 1)) d))) μ := by
    have hmap : Integrable (fun d => f (nonaffineHalf d)) (μ.map (nonaffineTranslation (dyadicHalf (dyadicInt 1)))) := by rw [ht]; exact hb
    exact (integrable_map_measure (hf.comp measurable_nonaffineHalf).aestronglyMeasurable (nonaffineTranslation _).continuous.measurable.aemeasurable).mp hmap
  have havg := integral_mono_ae ((hb.add hbt).div_const 2) hi (hu.mono (fun d hd => half_shortfall_average d hd))
  simp only [Pi.add_apply] at havg
  rw [integral_div,integral_add hb hbt] at havg
  have he := integral_invariant_translation μ (dyadicHalf (dyadicInt 1)) (ht _) (fun d => f (nonaffineHalf d)) (hf.comp measurable_nonaffineHalf)
  rw [he] at havg
  linarith
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence) (L:S.LimitLaws)
lemma backward_shortfall_moment (n:ℕ) :
    Integrable (fun d:NonAffineArray => arrayShortfall 0 (dyadicInt 1) d.val) (S.backwardLaw L n) ∧
    (∫d:NonAffineArray,arrayShortfall 0 (dyadicInt 1) d.val ∂S.backwardLaw L n)≤1 := by
  induction n with
  | zero => rw [S.backwardLaw_zero L]; exact S.terminal_shortfall_integrable_bound L
  | succ n ih =>
    rw [S.backwardLaw_succ L]
    obtain ⟨hi,hb⟩ := shortfall_half_moment _ (S.backwardLaw_unit L n) (S.backwardLaw_translate L n) ih.1
    exact ⟨hi,hb.trans ih.2⟩
lemma backward_cap_integrable {α:ℝ} (hα:0≤α) (hα1:α≤1) (n:ℕ) :
    Integrable (fun d:NonAffineArray => capF α d.val) (S.backwardLaw L n) := by
  obtain ⟨C,hC,hb⟩ := entropyCap_upper hα hα1
  exact ((S.backward_shortfall_moment L n).1.const_mul C).mono'
    ((continuous_capF α).comp continuous_subtype_val).aestronglyMeasurable (by
      filter_upwards [S.backwardLaw_unit L n] with d hd
      rw [Real.norm_eq_abs,capF,abs_of_nonneg (entropyCap_bounds hα hα1 (shortfall_unit_mem d.val hd _ _ (by norm_num))).1]
      exact hb _ (shortfall_unit_mem d.val hd _ _ (by norm_num)))
lemma backward_cap_difference {α:ℝ} (hα:0≤α) (hα1:α≤1) (n:ℕ) :
    (∫d:NonAffineArray,capG α d.val ∂S.backwardLaw L (n+1))=
      (∫d:NonAffineArray,capF α d.val ∂S.backwardLaw L n)-(∫d:NonAffineArray,capF α d.val ∂S.backwardLaw L (n+1)) := by
  have hm : (S.backwardLaw L (n+1)).map nonaffineDilate=S.backwardLaw L n := by
    rw [S.backwardLaw_succ L,map_dilate_half _ (S.backwardLaw_unit L n)]
  have hf : Measurable (fun d:NonAffineArray => capF α d.val) := (continuous_capF α).measurable.comp measurable_subtype_coe
  have h1 := S.backward_cap_integrable L hα hα1 (n+1)
  have hd : Integrable (fun d:NonAffineArray => capF α (nonaffineDilate d).val) (S.backwardLaw L (n+1)) := by
    apply (integrable_map_measure hf.aestronglyMeasurable continuous_nonaffineDilate.measurable.aemeasurable).mp
    rw [hm]; exact S.backward_cap_integrable L hα hα1 n
  have ht : Integrable (fun d:NonAffineArray => capF α (nonaffineTranslation (dyadicInt 1) d).val) (S.backwardLaw L (n+1)) := by
    apply (integrable_map_measure hf.aestronglyMeasurable (nonaffineTranslation _).continuous.measurable.aemeasurable).mp
    rw [S.backwardLaw_translate L]; exact h1
  simp_rw [capG_coboundary]
  have he := integral_sub hd ((h1.add ht).div_const 2)
  simp only [Pi.add_apply] at he
  change (∫d:NonAffineArray,capF α (nonaffineDilate d).val-(capF α d.val+capF α (nonaffineTranslation (dyadicInt 1) d).val)/2 ∂S.backwardLaw L (n+1))=_
  rw [he,integral_div]
  rw [integral_add h1 ht]
  rw [←integral_map continuous_nonaffineDilate.measurable.aemeasurable hf.aestronglyMeasurable,hm]
  rw [integral_invariant_translation _ _ (S.backwardLaw_translate L _ _) _ hf]
  ring
end CriticalScaleSequence
end StandardMapEntropy

end OAI
