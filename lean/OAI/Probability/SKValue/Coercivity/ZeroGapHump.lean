import Mathlib

namespace OAI

section
open Set
namespace SKValue
lemma positive_right_hump_impossible {f G:ℝ → ℝ} {a b x:ℝ}
    (hax:a<x) (hxb:x<b)
    (hGc:ContinuousOn G (Icc a b)) (hGd:∀t∈Ioo a b,HasDerivAt G (-f t) t)
    (hGb:G b=0) (hGx:0<G x) (hfa:f a=0)
    (hv:∀z∈Ioo a 1,z≤b → ConvexOn ℝ (Icc a z) f)
    (hend:∀s∈Ioo a b,0<f s → ∃z∈Ioo s 1,z≤b ∧ f z≤f s):False := by
  obtain ⟨s,hs,hes⟩:=exists_hasDerivAt_eq_slope G (fun t ↦ -f t) hxb
    (hGc.mono (Icc_subset_Icc hax.le le_rfl)) (fun t ht ↦ hGd t ⟨hax.trans ht.1,ht.2⟩)
  have hs0:0<f s := by
    rw [hGb,zero_sub] at hes
    have hh:=div_neg_of_neg_of_pos (neg_neg_of_pos hGx) (sub_pos.mpr hxb)
    linarith
  obtain ⟨z,hz,hzb,hfz⟩:=hend s ⟨hax.trans hs.1,hs.2⟩ hs0
  have has:a<s:=hax.trans hs.1
  have hav:a<z:=has.trans hz.1
  have hc:=hv z ⟨hav,hz.2⟩ hzb
  have hh:=hc.slope_mono_adjacent ⟨le_rfl,hav.le⟩ ⟨hav.le,le_rfl⟩ has hz.1
  have hl:0<(f s-f a)/(s-a):=div_pos (by rw [hfa,sub_zero];exact hs0) (sub_pos.mpr has)
  have hr:(f z-f s)/(z-s)≤0:=div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hfz) (sub_pos.mpr hz.1).le
  exact not_lt_of_ge (hh.trans hr) hl
end SKValue

end

end OAI
