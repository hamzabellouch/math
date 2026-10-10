import OAI.Probability.SLE.Loewner.InitialSlitFuture

namespace OAI

/-! Exact affine parameters for a segment of a prescribed simple arc. -/
noncomputable section
open Set Function

namespace SLEExactGauge

def slitSegmentParameter (s t : unitInterval) (hst : s≤t) (u : unitInterval) : unitInterval :=
  ⟨(s:ℝ)+((t:ℝ)-(s:ℝ))*(u:ℝ),by
    have hd : 0≤(t:ℝ)-(s:ℝ) := sub_nonneg.mpr hst
    constructor
    · exact add_nonneg s.property.1 (mul_nonneg hd u.property.1)
    · have hm := mul_le_mul_of_nonneg_left u.property.2 hd
      linarith [t.property.2]⟩

@[simp] lemma slitSegmentParameter_zero (s t : unitInterval) (hst : s≤t) :
    slitSegmentParameter s t hst 0=s := by
  apply Subtype.ext
  change (s:ℝ)+((t:ℝ)-(s:ℝ))*0=(s:ℝ)
  ring

@[simp] lemma slitSegmentParameter_one (s t : unitInterval) (hst : s≤t) :
    slitSegmentParameter s t hst 1=t := by
  apply Subtype.ext
  change (s:ℝ)+((t:ℝ)-(s:ℝ))*1=(t:ℝ)
  ring

lemma slitSegmentParameter_gt {s t : unitInterval} (hst : s<t)
    {u : unitInterval} (hu : u≠0) : s<slitSegmentParameter s t hst.le u := by
  change (s:ℝ)<(s:ℝ)+((t:ℝ)-(s:ℝ))*(u:ℝ)
  exact lt_add_of_pos_right _ (mul_pos (sub_pos.mpr hst) (unitInterval.pos_iff_ne_zero.mpr hu))

lemma slitSegmentParameter_le (s t : unitInterval) (hst : s≤t) (u : unitInterval) :
    slitSegmentParameter s t hst u≤t := by
  change (s:ℝ)+((t:ℝ)-(s:ℝ))*(u:ℝ)≤(t:ℝ)
  have hm := mul_le_mul_of_nonneg_left u.property.2
    (show 0≤(t:ℝ)-(s:ℝ) from sub_nonneg.mpr hst)
  linarith

lemma slitSegmentParameter_eq_future {s t : unitInterval} (hst : s<t) (ht : t<1)
    {u : unitInterval} (hu : u≠0) :
    slitFutureParameter s (((t:ℝ)-(s:ℝ))*(u:ℝ))=slitSegmentParameter s t hst.le u := by
  apply Subtype.ext
  apply slitFutureParameter_coe
  have hd : 0<(t:ℝ)-(s:ℝ) := sub_pos.mpr hst
  refine ⟨mul_pos hd (unitInterval.pos_iff_ne_zero.mpr hu),?_⟩
  have hm := mul_le_mul_of_nonneg_left u.property.2 hd.le
  have ht' : (t:ℝ)<1 := ht
  nlinarith

lemma exists_slitSegmentParameter {s t v : unitInterval} (hst : s<t) (hv : v∈Ioc s t) :
    ∃ u : unitInterval, u≠0 ∧ slitSegmentParameter s t hst.le u=v := by
  have hd : 0<(t:ℝ)-(s:ℝ) := sub_pos.mpr hst
  have hvs : 0<(v:ℝ)-(s:ℝ) := sub_pos.mpr (show (s:ℝ)<(v:ℝ) from hv.1)
  let u : unitInterval := ⟨((v:ℝ)-(s:ℝ))/((t:ℝ)-(s:ℝ)),
    (div_pos hvs hd).le,
    (div_le_one hd).mpr (sub_le_sub_right (show (v:ℝ)≤(t:ℝ) from hv.2) _)⟩
  refine ⟨u,?_,?_⟩
  · apply unitInterval.pos_iff_ne_zero.mp
    exact div_pos hvs hd
  · apply Subtype.ext
    change (s:ℝ)+((t:ℝ)-(s:ℝ))*(((v:ℝ)-(s:ℝ))/((t:ℝ)-(s:ℝ)))=(v:ℝ)
    field_simp
    ring

end SLEExactGauge

end

end OAI
