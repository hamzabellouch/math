import OAI.Dynamics.StandardMap.ScaleEvaluation

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma twoRay_real_properties {d:DistanceArray} {c:ℝ} (hu:UnitArray d) (hc:c<1) (hs:SlowShape (realArray d) c)
    (hd:d∈twoRayClass) : ExteriorUnitRays (realArray d) (endpointLeft d) (endpointRight d) ∧
    (∀s t:ℝ,s∈Icc (endpointLeft d) (endpointRight d) → t∈Icc (endpointLeft d) (endpointRight d) → realArray d s t≤c*|t-s|) := by
  rcases hs with hs|⟨a,hl,hs⟩|⟨b,hr,hs⟩|⟨a,b,hab,⟨hl,hr⟩,hs⟩
  · have hh := endpoints_slow (d:=d) hc (fun s t => by simpa only [realArray_coe d hu] using hs s t)
    exact (hd.1 hh.1).elim
  · have hh := endpoints_left_ray (d:=d) hc
      (fun s t hp hq => by simpa only [realArray_coe d hu] using hl s hp t hq)
      (fun s t hp hq => by simpa only [realArray_coe d hu] using hs s hp t hq)
    exact (hd.2.2.2 hh.2).elim
  · have hh := endpoints_right_ray (d:=d) hc
      (fun s t hp hq => by simpa only [realArray_coe d hu] using hr s hp t hq)
      (fun s t hp hq => by simpa only [realArray_coe d hu] using hs s hp t hq)
    exact (hd.1 hh.1).elim
  · have hh := endpoints_two_rays (d:=d) hab hc
      (fun s t hp hq => by simpa only [realArray_coe d hu] using hl s t hp hq)
      (fun s t hp hq => by simpa only [realArray_coe d hu] using hr s t hp hq)
      (fun s t hp hq => by simpa only [realArray_coe d hu] using hs s hp t hq)
    have ha : endpointLeft d=a := by simp only [endpointLeft,hh.1,EReal.toReal_coe]
    have hb : endpointRight d=b := by simp only [endpointRight,hh.2,EReal.toReal_coe]
    rw [ha,hb]
    exact ⟨⟨hl,hr⟩,fun s t hp hq => hs s hp t hq⟩
lemma band_shortfall_bound (d:NonAffineArray) (hd:d∈lengthBand 0)
    (hs:SlowShape (realArray d.val) (999/1000)) (ht:TreeArray d.val)
    (hc:NoFastCancellation (realArray d.val) (1/100000000)) (t:DyadicTime) (hp:0<(t:ℝ)) :
    arrayShortfall 0 t d.val≤1200000004/(t:ℝ) := by
  have hh := twoRay_real_properties hd.1 (by norm_num) hs hd.2.1
  have hab := (twoRay_properties hd.1 (by norm_num) hs hd.2.1).1
  have hb := (exterior_ray_shortfall (realArray_treeLine d.val hd.1 ht) hab.le (by norm_num) hh.1 hc 0 t hp).2
  have hlen : coreLength d.val<2 := by simpa only [lengthBand,zpow_zero,zero_add,zpow_one] using hd.2.2.2
  have hreal : realArray d.val 0 (0+(t:ℝ))=d.val.val 0 t := by
    simpa only [ZeroMemClass.coe_zero,zero_add] using realArray_coe d.val hd.1 (0:DyadicTime) t
  rw [hreal] at hb
  change 1-d.val.val 0 t/((t:ℝ)-0)≤_
  rw [sub_zero]
  apply hb.trans
  apply (div_le_div_iff_of_pos_right hp).mpr
  unfold coreLength at hlen
  norm_num at *
  linarith
lemma band_cap_support (α:ℝ) (d:NonAffineArray) (hd:d∈lengthBand 0)
    (hs:SlowShape (realArray d.val) (999/1000)) (t:DyadicTime) (hp:0<(t:ℝ))
    (he:endpointLeft d.val∉Icc (-2) (t:ℝ)) : entropyCap α (arrayShortfall 0 t d.val)=0 := by
  obtain ⟨hab,hl,hr,hslow⟩ := twoRay_properties hd.1 (by norm_num) hs hd.2.1
  have hlen : endpointRight d.val-endpointLeft d.val<2 := by simpa only [lengthBand,zpow_zero,zero_add,zpow_one,coreLength] using hd.2.2.2
  have hh : d.val.val 0 t=(t:ℝ) := by
    by_cases h:endpointLeft d.val<(t:ℝ)
    · have ha : endpointLeft d.val< -2 := by by_contra hn; exact he ⟨le_of_not_gt hn,h.le⟩
      have hrr := hr 0 t (by change endpointRight d.val≤0; linarith) (by linarith)
      simpa only [ZeroMemClass.coe_zero,sub_zero,abs_of_pos hp] using hrr
    · have hll := hl 0 t (by change (0:ℝ)≤endpointLeft d.val; linarith) (le_of_not_gt h)
      simpa only [ZeroMemClass.coe_zero,sub_zero,abs_of_pos hp] using hll
  have heq : arrayShortfall 0 t d.val=0 := by
    unfold arrayShortfall; rw [hh,ZeroMemClass.coe_zero,sub_zero,div_self hp.ne']; ring
  rw [heq,entropyCap_linear (by norm_num),mul_zero]
end StandardMapEntropy

end OAI
