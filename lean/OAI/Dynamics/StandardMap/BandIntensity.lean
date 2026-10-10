import OAI.Dynamics.StandardMap.EndpointIntensity

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped ENNReal Classical
namespace StandardMapEntropy
noncomputable def bandLaw (μ:Measure NonAffineArray) : Measure NonAffineArray := μ.restrict (lengthBand 0)
noncomputable def bandIntensity (μ:Measure NonAffineArray) : Measure ℝ := (bandLaw μ).map (fun d => endpointLeft d.val)
lemma bandLaw_translate (μ:Measure NonAffineArray) (ht:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) (r:DyadicTime) : (bandLaw μ).map (nonaffineTranslation r)=bandLaw μ :=
  map_restrict_invariant μ _ (nonaffineTranslation r).continuous.measurable (ht r) _ (measurableSet_lengthBand 0) (lengthBand_translate 0 r)
lemma bandIntensity_translate (μ:Measure NonAffineArray) (ht:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) (r:DyadicTime) : (bandIntensity μ).map (fun x:ℝ => x-(r:ℝ))=bandIntensity μ := by
  apply push_invariant _ _ (nonaffineTranslation r).continuous.measurable (bandLaw_translate μ ht r)
    _ (measurable_endpointLeft.comp measurable_subtype_coe) _ (measurable_id.sub measurable_const)
  exact (ae_restrict_mem (measurableSet_lengthBand 0)).mono (fun d hd => (endpointLeft_translate r d.val hd.2.1.2.1 hd.2.1.1).symm)
lemma bandIntensity_finite (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000)) : bandIntensity μ (Ico 0 1)<∞ := by
  have hbin (x:DyadicTime) (hx:0≤(x:ℝ)) :
      μ {d:NonAffineArray | d∈lengthBand 0 ∧ endpointLeft d.val∈Ico (x:ℝ) ((x:ℝ)+1/2)}<∞ := by
    apply lt_of_le_of_lt (measure_mono_ae ?_) (separated_secants_finite μ (dyadicInt (-1)) 0
      (x+dyadicHalf (dyadicInt 1)) (x+dyadicInt 1) (by norm_num) (by simp only [AddSubgroup.coe_add,dyadicHalf_val,dyadicInt_val,Int.cast_one]; linarith) (999/1000) (by norm_num))
    filter_upwards [hs] with d hsd
    rintro ⟨hd,ha⟩
    obtain ⟨hab,hl,hr,hslow⟩ := twoRay_properties hd.1 (by norm_num) hsd hd.2.1
    have hlen : 1≤endpointRight d.val-endpointLeft d.val := by simpa only [lengthBand,zpow_zero,coreLength] using hd.2.2.1
    refine ⟨?_,?_⟩
    · have hh := hl (dyadicInt (-1)) 0 (by norm_num; linarith [ha.1]) (by change (0:ℝ)≤endpointLeft d.val; linarith [ha.1])
      simpa only [dyadicInt_val,Int.cast_neg,Int.cast_one,ZeroMemClass.coe_zero,sub_neg_eq_add,zero_add,abs_of_pos (by norm_num : (0:ℝ)<1)] using hh
    · have hp : ((x+dyadicHalf (dyadicInt 1):DyadicTime):ℝ)=(x:ℝ)+1/2 := by simp only [AddSubgroup.coe_add,dyadicHalf_val,dyadicInt_val,Int.cast_one]
      have hq : ((x+dyadicInt 1:DyadicTime):ℝ)=(x:ℝ)+1 := by simp only [AddSubgroup.coe_add,dyadicInt_val,Int.cast_one]
      have hh := hslow (x+dyadicHalf (dyadicInt 1)) (x+dyadicInt 1)
        (by rw [hp]; constructor <;> linarith [ha.1,ha.2]) (by rw [hq]; constructor <;> linarith [ha.1,ha.2])
      rw [abs_of_pos (by rw [hp,hq]; linarith)] at hh
      exact hh
  have h0 := hbin 0 (by norm_num)
  have h1 := hbin (dyadicHalf (dyadicInt 1)) (by norm_num)
  change ((bandLaw μ).map (endpointLeft ∘ Subtype.val)) (Ico 0 1)<∞
  rw [Measure.map_apply (measurable_endpointLeft.comp measurable_subtype_coe) measurableSet_Ico,bandLaw,Measure.restrict_apply ((measurable_endpointLeft.comp measurable_subtype_coe) measurableSet_Ico)]
  apply lt_of_le_of_lt (measure_mono ?_) ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.mpr ⟨h0,h1⟩))
  rintro d ⟨ha,hd⟩
  by_cases h: endpointLeft d.val<1/2
  · exact Or.inl ⟨hd,by simpa only [mem_Ico,ZeroMemClass.coe_zero,zero_add,Function.comp_apply] using And.intro ha.1 h⟩
  · exact Or.inr ⟨hd,by simp only [mem_Ico,dyadicHalf_val,dyadicInt_val,Int.cast_one]; constructor; exact le_of_not_gt h; have ha1 : endpointLeft d.val<1 := ha.2; linarith⟩
lemma stationary_Ico_finite (μ:Measure ℝ)
    (ht:∀r:DyadicTime,μ.map (fun x:ℝ => x-(r:ℝ))=μ) (hf:μ (Ico 0 1)<∞) (a b:ℝ) : μ (Icc a b)<∞ := by
  obtain ⟨n,hn⟩ := exists_nat_gt (b-(⌊a⌋:ℤ))
  have he := stationary_Ico_nat μ ht ⌊a⌋ n
  apply lt_of_le_of_lt (measure_mono (t:=Ico (⌊a⌋:ℝ) ((⌊a⌋:ℝ)+n)) ?_) ?_
  · exact fun x hx => ⟨(Int.floor_le a).trans hx.1,by linarith [hx.2]⟩
  · rw [he]; exact ENNReal.mul_lt_top (by simp) hf
lemma bandLaw_endpoint_finite (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000))
    (ht:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) (a b:ℝ) :
    bandLaw μ {d:NonAffineArray | endpointLeft d.val∈Icc a b}<∞ := by
  have hh := stationary_Ico_finite (bandIntensity μ) (bandIntensity_translate μ ht) (bandIntensity_finite μ hs) a b
  change ((bandLaw μ).map (endpointLeft ∘ Subtype.val)) (Icc a b)<∞ at hh
  rw [Measure.map_apply (measurable_endpointLeft.comp measurable_subtype_coe) measurableSet_Icc] at hh
  exact hh
end StandardMapEntropy

end OAI
