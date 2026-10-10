import OAI.Dynamics.StandardMap.DyadicArrays

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace StandardMapEntropy
noncomputable def arrayTranslate (r : DyadicTime) (d : DistanceArray) : DistanceArray :=
  ⟨fun s t => d.val (s+r) (t+r),by
    obtain ⟨h0,hs,hsy,ht,hb⟩ := d.property
    refine ⟨fun s t => h0 _ _,fun s => hs _,fun s t => hsy _ _,fun s t u => ht _ _ _,?_⟩
    intro s t
    convert hb (s+r) (t+r) using 1
    congr 2
    change (t:ℝ)-(s:ℝ)=((t:ℝ)+(r:ℝ))-((s:ℝ)+(r:ℝ))
    ring⟩
lemma continuous_arrayTranslate (r : DyadicTime) : Continuous (arrayTranslate r) := by
  apply Continuous.subtype_mk
  apply continuous_pi; intro s
  apply continuous_pi; intro t
  exact continuous_arrayEval (s+r) (t+r)
@[simp] lemma arrayTranslate_zero (d : DistanceArray) : arrayTranslate 0 d=d := by
  apply Subtype.ext
  funext s t
  simp [arrayTranslate]
lemma arrayTranslate_add (r q : DyadicTime) (d : DistanceArray) :
    arrayTranslate r (arrayTranslate q d)=arrayTranslate (r+q) d := by
  apply Subtype.ext
  funext s t
  simp only [arrayTranslate,add_assoc]
noncomputable def arrayTranslation (r : DyadicTime) : DistanceArray ≃ₜ DistanceArray where
  toFun := arrayTranslate r
  invFun := arrayTranslate (-r)
  left_inv := by intro d; rw [arrayTranslate_add,neg_add_cancel,arrayTranslate_zero]
  right_inv := by intro d; rw [arrayTranslate_add,add_neg_cancel,arrayTranslate_zero]
  continuous_toFun := continuous_arrayTranslate r
  continuous_invFun := continuous_arrayTranslate (-r)
noncomputable def arrayDilate (d : DistanceArray) : DistanceArray :=
  ⟨fun s t => d.val (s+s) (t+t)/2,by
    obtain ⟨h0,hs,hsy,ht,hb⟩ := d.property
    refine ⟨fun s t => div_nonneg (h0 _ _) (by norm_num),?_,?_,?_,?_⟩
    · intro s; simp only [hs,zero_div]
    · intro s t; dsimp only; rw [hsy]
    · intro s t u; have := ht (s+s) (t+t) (u+u); dsimp only; linarith
    · intro s t
      have hh := hb (s+s) (t+t)
      change d.val (s+s) (t+t)≤|((t:ℝ)+(t:ℝ))-((s:ℝ)+(s:ℝ))|+2 at hh
      rw [show ((t:ℝ)+(t:ℝ))-((s:ℝ)+(s:ℝ))=2*((t:ℝ)-(s:ℝ)) by ring,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
      dsimp only; linarith⟩
lemma continuous_arrayDilate : Continuous arrayDilate := by
  apply Continuous.subtype_mk
  apply continuous_pi; intro s
  apply continuous_pi; intro t
  exact (continuous_arrayEval (s+s) (t+t)).div_const 2
@[simp] lemma arrayDilate_affine (w : Icc (0:ℝ) 1) : arrayDilate (affineArray w)=affineArray w := by
  apply Subtype.ext
  funext s t
  change (w.val*|((t:ℝ)+(t:ℝ))-((s:ℝ)+(s:ℝ))|)/2=w.val*|(t:ℝ)-(s:ℝ)|
  rw [show ((t:ℝ)+(t:ℝ))-((s:ℝ)+(s:ℝ))=2*((t:ℝ)-(s:ℝ)) by ring,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  ring
@[simp] lemma arrayTranslate_affine (r : DyadicTime) (w : Icc (0:ℝ) 1) : arrayTranslate r (affineArray w)=affineArray w := by
  apply Subtype.ext
  funext s t
  change w.val*|((t:ℝ)+(r:ℝ))-((s:ℝ)+(r:ℝ))|=w.val*|(t:ℝ)-(s:ℝ)|
  congr 2; ring
lemma arrayDilate_mem_affine_iff (d : DistanceArray) : arrayDilate d∈affineLocus ↔ d∈affineLocus := by
  constructor
  · rintro ⟨w,hw⟩
    refine ⟨w,?_⟩
    apply Subtype.ext
    funext s t
    have he := congrArg (fun d : DistanceArray => d.val (dyadicHalf s) (dyadicHalf t)) hw
    change w.val*|((t:ℝ)/2)-((s:ℝ)/2)|=d.val (dyadicHalf s+dyadicHalf s) (dyadicHalf t+dyadicHalf t)/2 at he
    rw [dyadicHalf_add_self,dyadicHalf_add_self,← sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at he
    change w.val*|(t:ℝ)-(s:ℝ)|=d.val s t
    linarith
  · rintro ⟨w,rfl⟩; exact ⟨w,(arrayDilate_affine w).symm⟩
noncomputable def arrayShortfall (s t : DyadicTime) (d : DistanceArray) : ℝ :=
  1-d.val s t/((t:ℝ)-(s:ℝ))
noncomputable def arrayJ (s t : DyadicTime) (d : DistanceArray) : ℝ :=
  arrayShortfall s t d-(arrayShortfall s (dyadicMid s t) d+arrayShortfall (dyadicMid s t) t d)/2
noncomputable def arrayV (s t : DyadicTime) (d : DistanceArray) : ℝ :=
  (arrayShortfall s (dyadicMid s t) d-arrayShortfall (dyadicMid s t) t d)^2
lemma continuous_arrayShortfall (s t : DyadicTime) : Continuous (arrayShortfall s t) :=
  continuous_const.sub ((continuous_arrayEval s t).div_const _)
lemma continuous_arrayJ (s t : DyadicTime) : Continuous (arrayJ s t) :=
  (continuous_arrayShortfall s t).sub (((continuous_arrayShortfall s (dyadicMid s t)).add
    (continuous_arrayShortfall (dyadicMid s t) t)).div_const 2)
lemma continuous_arrayV (s t : DyadicTime) : Continuous (arrayV s t) :=
  ((continuous_arrayShortfall s (dyadicMid s t)).sub (continuous_arrayShortfall (dyadicMid s t) t)).pow 2
lemma arrayJ_eq (s t : DyadicTime) (hst : (s:ℝ)<(t:ℝ)) (d : DistanceArray) :
    arrayJ s t d=(d.val s (dyadicMid s t)+d.val (dyadicMid s t) t-d.val s t)/((t:ℝ)-(s:ℝ)) := by
  unfold arrayJ arrayShortfall
  rw [dyadicMid_val]
  have h1 : (t:ℝ)-(s:ℝ)≠0 := sub_ne_zero.mpr hst.ne'
  have h2 : ((s:ℝ)+(t:ℝ))/2-(s:ℝ)≠0 := by linarith
  have h3 : (t:ℝ)-((s:ℝ)+(t:ℝ))/2≠0 := by linarith
  rw [show ((s:ℝ)+(t:ℝ))/2-(s:ℝ)=((t:ℝ)-(s:ℝ))/2 by ring,
    show (t:ℝ)-((s:ℝ)+(t:ℝ))/2=((t:ℝ)-(s:ℝ))/2 by ring]
  field_simp [h1]; ring
lemma arrayJ_nonneg (s t : DyadicTime) (hst : (s:ℝ)<(t:ℝ)) (d : DistanceArray) : 0≤arrayJ s t d := by
  rw [arrayJ_eq s t hst d]
  exact div_nonneg (sub_nonneg.mpr (d.property.2.2.2.1 _ _ _)) (sub_pos.mpr hst).le
lemma arrayV_nonneg (s t : DyadicTime) (d : DistanceArray) : 0≤arrayV s t d := sq_nonneg _
lemma array_zero_test_halves (s t : DyadicTime) (hst : (s:ℝ)<(t:ℝ)) (d : DistanceArray)
    (hzero : arrayJ s t d+arrayV s t d=0) :
    d.val s (dyadicMid s t)=d.val s t/2 ∧ d.val (dyadicMid s t) t=d.val s t/2 := by
  have hJ : arrayJ s t d=0 := by linarith [arrayJ_nonneg s t hst d,arrayV_nonneg s t d]
  have hV : arrayV s t d=0 := by linarith
  have he : arrayShortfall s (dyadicMid s t) d=arrayShortfall (dyadicMid s t) t d := by
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hV)
  rw [arrayJ_eq s t hst d] at hJ
  have hsum : d.val s (dyadicMid s t)+d.val (dyadicMid s t) t=d.val s t := by
    have := (div_eq_zero_iff.mp hJ).resolve_right (sub_ne_zero.mpr hst.ne')
    linarith
  unfold arrayShortfall at he
  rw [dyadicMid_val] at he
  have hm : ((s:ℝ)+(t:ℝ))/2-(s:ℝ)=((t:ℝ)-(s:ℝ))/2 := by ring
  have hm' : (t:ℝ)-((s:ℝ)+(t:ℝ))/2=((t:ℝ)-(s:ℝ))/2 := by ring
  rw [hm,hm'] at he
  have hn : ((t:ℝ)-(s:ℝ))/2≠0 := by positivity
  have he' : d.val s (dyadicMid s t)=d.val (dyadicMid s t) t := (div_left_inj' hn).mp (by linarith)
  constructor <;> linarith
end StandardMapEntropy

end OAI
