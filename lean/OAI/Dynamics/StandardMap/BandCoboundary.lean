import OAI.Dynamics.StandardMap.BandSeries

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped ENNReal Classical
namespace StandardMapEntropy
noncomputable def bandMoment (μ:Measure NonAffineArray) (α:ℝ) (j:ℤ) : ℝ :=
  ∫d,bandCap α (dyadicZoom j (dyadicInt 1)) d ∂bandLaw μ
lemma zoom_one_pos (j:ℤ) : 0<(dyadicZoom j (dyadicInt 1):ℝ) := by
  rw [dyadicZoom_val,dyadicInt_val,Int.cast_one,mul_one]; positivity
lemma zoom_next (j:ℤ) : dyadicZoom (j+1) (dyadicInt 1)=dyadicZoom j (dyadicInt 1)+dyadicZoom j (dyadicInt 1) := by
  rw [dyadicZoom_succ,dyadicZoom_add]
lemma bandCap_translate (α:ℝ) (t:DyadicTime) (d:NonAffineArray) :
    bandCap α t (nonaffineTranslation t d)=entropyCap α (arrayShortfall t (t+t) d.val) := by
  unfold bandCap
  change entropyCap α (arrayShortfall 0 t (arrayTranslate t d.val))=_
  rw [shortfall_translate,zero_add]
lemma band_coboundary (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000))
    (hT:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) {α:ℝ} (ha:0≤α) (ha1:α≤1) (j:ℤ) :
    (∫d,capG α (scaleZ j d).val ∂bandLaw μ)=bandMoment μ α (j+1)-bandMoment μ α j := by
  let t:=dyadicZoom j (dyadicInt 1)
  let u:=dyadicZoom (j+1) (dyadicInt 1)
  have hi:=bandCap_integrable μ hs hT ha ha1 t (zoom_one_pos j)
  have hj:=bandCap_integrable μ hs hT ha ha1 u (zoom_one_pos (j+1))
  have ht:Integrable (fun d => bandCap α t (nonaffineTranslation t d)) (bandLaw μ) := by
    apply (integrable_map_measure (measurable_bandCap α t).aestronglyMeasurable (nonaffineTranslation t).continuous.measurable.aemeasurable).mp
    rw [bandLaw_translate μ hT]; exact hi
  have he : (fun d:NonAffineArray => capG α (scaleZ j d).val)=ᵐ[bandLaw μ]
      (fun d => bandCap α u d-(bandCap α t d+bandCap α t (nonaffineTranslation t d))/2) := by
    filter_upwards [ae_restrict_mem (measurableSet_lengthBand 0)] with d hd
    rw [scaleZ_capG α j d hd.1,bandCap_translate]
    simp only [bandCap,u,t,zoom_next]
  have hsum : Integrable (fun d => (bandCap α t d+bandCap α t (nonaffineTranslation t d))/2) (bandLaw μ) := (hi.add ht).div_const 2
  rw [integral_congr_ae he,integral_sub hj hsum,integral_div,integral_add hi ht]
  rw [integral_invariant_translation _ _ (bandLaw_translate μ hT t) _ (measurable_bandCap α t)]
  change bandMoment μ α (j+1)-(bandMoment μ α j+bandMoment μ α j)/2=_
  ring
end StandardMapEntropy

end OAI
