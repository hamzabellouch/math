import OAI.Dynamics.StandardMap.RescaledArrays

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
noncomputable def sampleLaw (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n) : Measure DistanceArray :=
  area.map (fun z => sampleArray k hk z n hn)
instance sampleLawProbability (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n) :
    IsProbabilityMeasure (sampleLaw k hk n hn) := by
  unfold sampleLaw
  exact (Measure.isProbabilityMeasure_map_iff (continuous_sampleArray k hk n hn).measurable.aemeasurable).2 inferInstance
lemma integral_sampleLaw (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n) (F : DistanceArray → ℝ)
    (hF : Continuous F) :
    (∫ d,F d ∂sampleLaw k hk n hn)=∫ z,F (sampleArray k hk z n hn) ∂area :=
  integral_map_of_stronglyMeasurable (continuous_sampleArray k hk n hn).measurable hF.stronglyMeasurable
lemma sampleLaw_dilate (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n) :
    (sampleLaw k hk n hn).map arrayDilate=sampleLaw k hk (n+n) (by omega) := by
  unfold sampleLaw
  rw [Measure.map_map continuous_arrayDilate.measurable (continuous_sampleArray k hk n hn).measurable]
  congr 1
  funext z
  exact sampleArray_dilate k hk z n hn
lemma sampleLaw_translate (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n)
    (r : DyadicTime) (a : ℤ) (ha : (n:ℝ)*(r:ℝ)=(a:ℝ)) :
    (sampleLaw k hk n hn).map (arrayTranslate r)=sampleLaw k hk n hn := by
  unfold sampleLaw
  rw [Measure.map_map (continuous_arrayTranslate r).measurable (continuous_sampleArray k hk n hn).measurable]
  have he : (arrayTranslate r) ∘ (fun z => sampleArray k hk z n hn)=
      (fun z => sampleArray k hk z n hn) ∘ (torusIter k a) := by
    funext z; exact sampleArray_translate k hk z n hn r a ha
  rw [he,← Measure.map_map (continuous_sampleArray k hk n hn).measurable (continuous_torusIter k a).measurable,
    (measurePreserving_torusIter k a).map_eq]
lemma shortfall_sample_aligned (k : ℝ) (hk : 0≤k) (z : Torus) (n : ℕ) (hn : 0<n)
    (s t : DyadicTime) (a : ℤ) (m : ℕ) (hm : 0 < m)
    (hs : (n:ℝ)*(s:ℝ)=(a:ℝ)) (ht : (n:ℝ)*(t:ℝ)=(a:ℝ)+(m:ℝ)) :
    arrayShortfall s t (sampleArray k hk z n hn)=torusShortfall k z a m := by
  have hni : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have hlen : (t:ℝ)-(s:ℝ)=(m:ℝ)/(n:ℝ) := (eq_div_iff hni).mpr (by nlinarith)
  unfold arrayShortfall
  change 1-rescaledDistance k z n s t/((t:ℝ)-(s:ℝ))=_
  rw [rescaledDistance_aligned k z n s t a (a+(m:ℤ)) hs (by simpa only [Int.cast_add,Int.cast_natCast] using ht),hlen,
    productDistance_forward]
  unfold torusShortfall
  field_simp
lemma integral_shortfall_sample (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n)
    (s t : DyadicTime) (a : ℤ) (m : ℕ) (hm : 0 < m)
    (hs : (n:ℝ)*(s:ℝ)=(a:ℝ)) (ht : (n:ℝ)*(t:ℝ)=(a:ℝ)+(m:ℝ)) :
    (∫ d,arrayShortfall s t d ∂sampleLaw k hk n hn)=meanDeficit k m := by
  rw [integral_sampleLaw k hk n hn _ (continuous_arrayShortfall s t)]
  simp_rw [shortfall_sample_aligned k hk _ n hn s t a m hm hs ht]
  have he (z : Torus) : torusShortfall k z a m=torusShortfall k (torusIter k a z) 0 m := by
    rw [torusShortfall_shift,zero_add]
  simp_rw [he]
  rw [integral_torusIter k a (fun z => torusShortfall k z 0 m),← meanDeficit_eq_integral_shortfall k hk m]
end StandardMapEntropy

end OAI
