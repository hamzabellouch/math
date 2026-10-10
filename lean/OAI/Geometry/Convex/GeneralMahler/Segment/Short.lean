import OAI.Geometry.Convex.GeneralMahler.Segment.First

namespace OAI
/-! Completion of short widths (≤.16), with explicit rounded budgets. -/
noncomputable section
open Set Filter Real MeasureTheory
namespace GeneralMahler.SCal.SE
open Tag Grid Jet Profile Segment
variable (H:NG)(m:ℝ) {h:ℝ}

include H in
lemma endDa (hh:0<h):
    let v:=seg m h
    |cd0 v|≤247/1000*h ∧ |qu v.2-qu v.1|≤2*(193/1000)*h:=by
  intro v
  have h1 : left m h ≤ right m h:=by unfold left right; linarith
  have hi {f:ℝ→ℝ} (hf:TestF f)(a:ℝ)(ha:∀ x,|DotF f x| ≤ a): |f v.2-f v.1|≤a*(2*h) :=by
    have hi:=dist_bdd hf _ h1 (fun t _=>ha t)
    rw [show right m h - left m h=2*h by unfold right left; ring] at hi; exact hi
  have he:=hi testC (247/1000) (fun t=> by
    apply abs_le.mpr
    have hi:=hdC H t; norm_num at *; exact hi)
  have hh:=hi (hqt H) (193/1000) (fun t=>by
    apply abs_le.mpr
    have hi:=SE.hdQ H t; norm_num at *; exact hi)
  unfold cd0; rw [abs_div]; norm_num;constructor<;> linarith

include H in
lemma CDa (hh:0<h)(he:h≤16/100):
    let v:=seg m h
    |ca0 v| ≤(321/1000)*h^2 ∧ |bd0 v|≤ (73/1000)*h^3 :=by
  intro v
  have hi:= chAbs m hh he testC (a:=95/100) (by positivity) fun x=> by
    apply abs_le.mpr; have hi:=hNC H x; norm_num at *; exact hi
  have hj:= chAbs m hh he (hqt H) (a:=56/100) (by positivity) fun x=>by
    apply abs_le.mpr
    have hq := hNQ H x
    norm_num at hq ⊢
    exact hq
  have hv:= (endDa H m hh).2
  constructor
  · have hc:ca0 v=bav Cp v-(Cp v.1+Cp v.2)/2:=by unfold ca0;ring
    rw [hc]; change |_| ≤ _ at hi; change |bav Cp _- _|≤_
    unfold v; nlinarith
  have he : bd0 v=(qu v.1-qu v.2)*(bav qu v-(qu v.1+qu v.2)/2):=by
    unfold bd0 qPlus mdis sqav
    rw [bav_sym (hqt H) v,bav_sym (sq_test (hqt H)) v]
    simp only [Prod.snd_swap]; ring
  rw [he,abs_mul,abs_sub_comm (qu v.1)]
  apply le_trans (mul_le_mul hv hj (abs_nonneg _) (by positivity))
  nlinarith [show 0≤h^3 by positivity]

lemma smallF (hh:0<h)(he:h≤16/100):
    (315/1000)*h^2≤fstar h:=by
  apply le_trans _ (sfL hh)
  unfold ubase
  rw [show wp*h^2/3*qsmall h=(wp/3*qsmall h)*h^2 from by ring]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  unfold qsmall;rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
  unfold wp r Profile.omegaP; norm_num; nlinarith
-- overcome relaxed C''
include H in
lemma cost_small (hh:0<h)(he:h≤16/100):
    costs (seg m h)<(1+tmax)*fstar h:= by
  let v:=seg m h
  obtain ⟨h1,h2⟩:=CDa H m hh he
  obtain ⟨h3,h4⟩:=endDa H m hh
  obtain ⟨hp,hd,_⟩:= init_phase m h hh
  have hb:=smallD m hh
  have hk:=smallU m H hh he
  obtain ⟨ha,hah⟩:=pa_short m hh (by linarith)
  obtain ⟨hv,hvh⟩:=ba_short H m hh (by linarith)
  change costs _ < _
  let u:=h^2
  have hu:0<u:=by unfold u;positivity
  have hue: h^2≤ (16/100:ℝ)^2 :=by nlinarith
  have haa:pa v≤1367/1000*h^2:= by
    unfold wp Profile.r Profile.omegaP at *; norm_num at *
    unfold v
    nlinarith [mul_le_mul_of_nonneg_left hue (sq_nonneg h)]
  have hba:ba v≤50/1000*h^2:= by
    unfold v; nlinarith [mul_le_mul_of_nonneg_left hue (sq_nonneg h)]
  have hdp:|pd v|≤683/1000*h^3:= by
    unfold v; rw [hd]
    unfold ubase wp Profile.omegaP Profile.r at *
    norm_num at *; nlinarith [show 0<h^3 by positivity]
  have hs:|ca0 v-pa v-ba v| ≤1738/1000*h^2 := by
    apply abs_le.mpr
    change |ca0 v|≤ _ at h1
    change 0≤ pa v at ha;change 0 ≤ ba v at hv
    have hh:=abs_le.mp h1; constructor <;> linarith [hh.1,hh.2]
  have ht:|cd0 v-pd v-bd0 v| ≤267/1000*h:= by
    apply abs_le.mpr
    change |cd0 v|≤ _ at h3; change |bd0 v|≤_ at h2
    obtain ⟨h1,h2⟩:=abs_le.mp h2; obtain ⟨h3,h4⟩:=abs_le.mp h3
    obtain ⟨h5,h6⟩:=abs_le.mp hdp
    constructor<;> nlinarith [mul_le_mul_of_nonneg_left hue hh.le]
  have X: (ca0 v-pa v-ba v)^2 ≤(1738/1000*h^2)^2 := sq_le_sq.2 (hs.trans (le_abs_self _))
  have Y: (cd0 v-pd v-bd0 v)^2≤(267/1000*h)^2:=sq_le_sq.2 (ht.trans (le_abs_self _))
  have hf:=smallF hh he
  change costs v < _
  change ek v+_≤ _ at hk
  unfold costs tmax lam ubase wp r Profile.omegaP at *
  norm_num at *
  unfold u v at *; nlinarith [mul_le_mul_of_nonneg_left hue (sq_nonneg h)]

lemma reduce_f (hH:LayerOK)(hh:0<h)
    (hc:costs (seg m h)<(1+tmax)*fstar h):symR (seg m h)<0:=by
  let v:=seg m h
  rw [lid4 _ hH]
  obtain ⟨_,_,hk⟩:=init_phase m h hh
  have hv:=vge m h hH.q_test
  unfold vsum; unfold tmax at *;linarith
include H in
lemma short (hh:0<h)(he:h≤16/100):symR (seg m h)<0:=
  reduce_f m (hSeg01 H) hh (cost_small H m hh he)
end GeneralMahler.SCal.SE

end

end OAI
