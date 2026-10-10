import OAI.Dynamics.StandardMap.ScaleEndpoints

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma separated_secants_compact (p q u v:DyadicTime) (hpq:(p:ℝ)<(q:ℝ)) (huv:(u:ℝ)<(v:ℝ))
    (c:ℝ) (hc:c<1) : IsCompact {d:NonAffineArray | d.val.val p q=(q:ℝ)-(p:ℝ) ∧ d.val.val u v≤c*((v:ℝ)-(u:ℝ))} := by
  let K:Set DistanceArray := {d | d.val p q=(q:ℝ)-(p:ℝ) ∧ d.val u v≤c*((v:ℝ)-(u:ℝ))}
  have hK : IsCompact K := ((isClosed_eq (continuous_arrayEval p q) continuous_const).inter
    (isClosed_le (continuous_arrayEval u v) continuous_const)).isCompact
  have hsub : K⊆(affineLocus)ᶜ := by
    intro d hd ⟨w,hw⟩
    subst d
    have h1 : w.val*((q:ℝ)-(p:ℝ))=(q:ℝ)-(p:ℝ) := by
      simpa only [affineArray,abs_of_pos (sub_pos.mpr hpq)] using hd.1
    have hw1 : w.val=1 := by nlinarith [sub_pos.mpr hpq]
    have h2 : w.val*((v:ℝ)-(u:ℝ))≤c*((v:ℝ)-(u:ℝ)) := by
      simpa only [affineArray,abs_of_pos (sub_pos.mpr huv)] using hd.2
    rw [hw1,one_mul] at h2
    exact (not_le_of_gt (mul_lt_of_lt_one_left (sub_pos.mpr huv) hc)) h2
  have hsub' : K⊆Set.range ((↑):NonAffineArray→DistanceArray) := fun d hd => ⟨⟨d,hsub hd⟩,rfl⟩
  exact IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK hsub'
lemma separated_secants_finite (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (p q u v:DyadicTime) (hpq:(p:ℝ)<(q:ℝ)) (huv:(u:ℝ)<(v:ℝ)) (c:ℝ) (hc:c<1) :
    μ {d:NonAffineArray | d.val.val p q=(q:ℝ)-(p:ℝ) ∧ d.val.val u v≤c*((v:ℝ)-(u:ℝ))}<∞ :=
  (separated_secants_compact p q u v hpq huv c hc).measure_lt_top
lemma one_left_interface_finite (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hu:∀ᵐd ∂μ,UnitArray d.val) (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000)) :
    μ {d:NonAffineArray | d.val∈leftRayClass ∧ endpointLeft d.val∈Ico (0:ℝ) 1}<∞ := by
  apply lt_of_le_of_lt (measure_mono_ae ?_) (separated_secants_finite μ (dyadicInt (-1)) 0 (dyadicInt 1) (dyadicInt 2) (by norm_num) (by norm_num) (999/1000) (by norm_num))
  filter_upwards [hu,hs] with d hud hsd
  rintro ⟨hd,ha⟩
  obtain ⟨hl,hslow⟩ := leftRay_properties hud (by norm_num) hsd hd
  refine ⟨?_,?_⟩
  · have hh := hl (dyadicInt (-1)) 0 (by norm_num; linarith [ha.1]) (by exact ha.1)
    simpa only [dyadicInt_val,Int.cast_neg,Int.cast_one,ZeroMemClass.coe_zero,sub_neg_eq_add,zero_add,abs_of_pos (by norm_num : (0:ℝ)<1)] using hh
  · have hh := hslow (dyadicInt 1) (dyadicInt 2) (by norm_num; exact ha.2.le) (by norm_num; linarith [ha.2])
    simpa only [dyadicInt_val,Int.cast_one,Int.cast_ofNat,abs_of_pos (by norm_num : (0:ℝ)<2-1)] using hh
lemma one_right_interface_finite (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hu:∀ᵐd ∂μ,UnitArray d.val) (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000)) :
    μ {d:NonAffineArray | d.val∈rightRayClass ∧ endpointRight d.val∈Ico (0:ℝ) 1}<∞ := by
  apply lt_of_le_of_lt (measure_mono_ae ?_) (separated_secants_finite μ (dyadicInt 1) (dyadicInt 2) (dyadicInt (-1)) 0 (by norm_num) (by norm_num) (999/1000) (by norm_num))
  filter_upwards [hu,hs] with d hud hsd
  rintro ⟨hd,hb⟩
  obtain ⟨hr,hslow⟩ := rightRay_properties hud (by norm_num) hsd hd
  refine ⟨?_,?_⟩
  · have hh := hr (dyadicInt 1) (dyadicInt 2) (by norm_num; exact hb.2.le) (by norm_num; linarith [hb.2])
    simpa only [dyadicInt_val,Int.cast_one,Int.cast_ofNat,abs_of_pos (by norm_num : (0:ℝ)<2-1)] using hh
  · have hh := hslow (dyadicInt (-1)) 0 (by norm_num; linarith [hb.1]) (by exact hb.1)
    simpa only [dyadicInt_val,Int.cast_neg,Int.cast_one,ZeroMemClass.coe_zero,sub_neg_eq_add,zero_add,abs_of_pos (by norm_num : (0:ℝ)<1)] using hh
end StandardMapEntropy

end OAI
