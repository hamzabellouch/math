import OAI.Dynamics.StandardMap.OneRayZero

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma shape_nonzero_cap_in_band {α:ℝ} {d:NonAffineArray} (hu:UnitArray d.val)
    (hs:SlowShape (realArray d.val) (999/1000))
    (hl:d.val∉leftRayClass) (hr:d.val∉rightRayClass) (hg:capG α d.val≠0) :
    d∈⋃j:ℤ,lengthBand (-j) := by
  rcases slowShape_dyadic hu hs with hslow|⟨a,hleft,hslow⟩|⟨b,hright,hslow⟩|⟨a,b,hab,hleft,hright,hslow⟩
  · exact (hg (capG_slow hslow)).elim
  · have he:=endpoints_left_ray (by norm_num : (999/1000:ℝ)<1) hleft hslow
    exact (hl (by change leftEndpoint d.val≠⊥ ∧ leftEndpoint d.val≠⊤ ∧ rightEndpoint d.val=⊤; rw [he.1,he.2]; simp)).elim
  · have he:=endpoints_right_ray (by norm_num : (999/1000:ℝ)<1) hright hslow
    exact (hr (by change leftEndpoint d.val=⊥ ∧ rightEndpoint d.val≠⊥ ∧ rightEndpoint d.val≠⊤; rw [he.1,he.2]; simp)).elim
  · have he:=endpoints_two_rays hab (by norm_num : (999/1000:ℝ)<1) hleft hright hslow
    have hd:d.val∈twoRayClass := by
      change leftEndpoint d.val≠⊥ ∧ leftEndpoint d.val≠⊤ ∧ rightEndpoint d.val≠⊥ ∧ rightEndpoint d.val≠⊤
      rw [he.1,he.2]; simp
    apply mem_union_lengthBand hu hd
    simp only [coreLength,endpointLeft,endpointRight,he.1,he.2,EReal.toReal_coe]
    exact sub_pos.mpr hab
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence) (L:S.LimitLaws)
lemma remainder_cap_band (α:ℝ) :
    (∫d:NonAffineArray,capG α d.val ∂S.remainderLaw L)=
      ∫d in ⋃j:ℤ,lengthBand (-j),capG α d.val ∂S.remainderLaw L := by
  have he :(fun d:NonAffineArray => capG α d.val)=ᵐ[S.remainderLaw L]
      (⋃j:ℤ,lengthBand (-j)).indicator (fun d => capG α d.val) := by
    have hl:∀ᵐd ∂S.remainderLaw L,d.val∉leftRayClass := ae_iff.mpr (by simpa only [not_not] using S.remainder_left_ray_zero L)
    have hr:∀ᵐd ∂S.remainderLaw L,d.val∉rightRayClass := ae_iff.mpr (by simpa only [not_not] using S.remainder_right_ray_zero L)
    filter_upwards [S.remainder_unit L,S.remainder_shape L,hl,hr] with d hd hs hl hr
    by_cases hg:capG α d.val=0
    · simp only [hg,Set.indicator_apply]; split_ifs <;> rfl
    · exact (Set.indicator_of_mem (shape_nonzero_cap_in_band hd hs hl hr hg) (fun d : NonAffineArray => capG α d.val)).symm
  rw [integral_congr_ae he,integral_indicator (MeasurableSet.iUnion (fun j => measurableSet_lengthBand (-j)))]
lemma remainder_cap_nonpos {α:ℝ} (ha:0≤α) (ha1:α≤1) (hasmall:α*1200000004≤1/16) :
    (∫d:NonAffineArray,capG α d.val ∂S.remainderLaw L)≤0 := by
  have:=S.remainder_local L
  have hser:=band_integral_series (S.remainderLaw L) (S.remainder_unit L) (S.remainder_dilate L)
    (fun d => capG α d.val) (S.capG_integrable_remainder L α)
  simp_rw [band_coboundary _ (S.remainder_shape L) (S.remainder_translate L) ha ha1] at hser
  rw [←S.remainder_cap_band L α] at hser
  apply bilateral_coboundary_nonpos _ _ hser
  exact bandMoment_order _ (S.remainder_shape L) (S.remainder_translate L)
    (ae_mono (S.remainder_le L) (S.tree_aemulti L))
    (ae_mono (S.remainder_le L) (S.noCancellation_aemulti L)) ha ha1 hasmall
end CriticalScaleSequence
end StandardMapEntropy

end OAI
