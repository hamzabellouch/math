import OAI.Geometry.Convex.GeneralMahler.Segment.Average
import OAI.Geometry.Convex.GeneralMahler.Segment.FarArc

namespace OAI
/-! §08 the unbounded segments, central-with-distant and tails opposite. -/
noncomputable section
open Set Filter Real MeasureTheory
namespace GeneralMahler.SCal.SE
open Tag Grid Profile Jet Segment
variable (H:NG)(m:ℝ){h:ℝ}
lemma Psmall (H:NG)(m:ℝ){h:ℝ}(hh:0 < h) :
    let v:=seg m h
    0≤ba v∧ ba v≤32/1000∧ |bd0 v|≤16/1000:=by
  intro v
  have h₁ (t):775/10000≤ qu (xs t)∧qu (xs t)≤2559/10000:=hQ H t
  obtain ⟨hp,hq⟩:=plusR H (m:=m) hh.le _ _ (fun x _=>h₁ x)
  change qPlus v∈_ at hp;change qPlus v.swap ∈ _ at hq
  obtain ⟨ha,hb⟩:=hp; obtain ⟨hc,hd⟩:=hq
  unfold ba bd0
  rw [abs_le]
  norm_num at *;refine ⟨?_,?_,?_,?_⟩<;> linarith

lemma sCase1 (H:NG)(m h:ℝ)
    (he:|left m h|≤14/10) (hr:36/10 ≤ right m h):
    costs (seg m h) < (1+tmax)*fstar h := by
  let v:=seg m h;let x:=left m h;let y:=right m h
  have hH:11/10 ≤ h:=by unfold left right at *; linarith [(abs_le.mp he).2]
  have hh:0<h:=by linarith
  obtain ⟨hkp,hk⟩:=hK H x
  obtain ⟨hcl,hc⟩:=hC H x
  obtain ⟨hf0,hf1,hg,hg',_,_⟩:=ValY H y hr
  let e := Cp v.2-Cp v.1
  change _ ≤ Kp v.1 at hkp
  change Kp v.1 ≤_ at hk
  change _ ≤ Cp v.1 at hcl
  change Cp v.1 ≤_ at hc
  change _≤ Kp v.2 at hf0
  change Kp v.2≤_ at hf1
  change _≤ Cp v.2 at hg
  change Cp v.2≤ _ at hg'
  have hE : -(160/1000:ℝ) ≤ e ∧ e≤160/1000 := by unfold e; constructor<;>linarith
  obtain ⟨hf,hpa,hpb,hpd⟩:=arc11 m hH
  have hi : Yval (Kp v.1) (Kp v.2) e ≤ (60/10000:ℝ):=
    Ybound _ _ _ _ _ _ _ _ _ _ hkp hk hf0 hf1 hE.1 hE.2 (by
      intro x hx y hy z hz; simp only [mem_insert_iff,mem_singleton_iff] at *
      rcases hx with hx|hx<;> rcases hy with hy|hy<;> rcases hz with hz|hz<;>
        rw [hx,hy,hz]<;> norm_num [Yval,mstar,tc,Profile.tr])
  have hg0:ek v+sgamma v≤144/10000:= by
    have hmv: bav Kp v≤84/10000:= avK H hh he hr
    rw [EK_eq]; change _+Yval _ _ e≤ _
    linarith
  obtain ⟨h₁,h₂,h₃⟩:= Psmall H m hh
  have ha: seg m h=v:=rfl
  rw [ha] at h₁ h₂ h₃
  obtain ⟨hz,hu,-⟩:= init_phase m h hh
  rw [ha] at hz hu
  rw [← hz] at hpa hpb; rw [← hu] at hpd
  have ht: -5010/10000 ≤ bav Cp v∧ bav Cp v ≤ -3410/10000 :=
    segR Cp testC hh.le _ _ (fun t _=>hC H t)
  have Hc : -(81/1000)≤ ca0 v∧ca0 v≤160/1000:=by
    unfold ca0; constructor<;> linarith [ht.1,ht.2]
  have Hd : |cd0 v|≤ 80/1000:=by
    change |e/2|≤_; rw [abs_le];constructor<;>linarith [hE.1,hE.2]
  have hs: |ca0 v-pa v-ba v|≤221/1000:=by rw [abs_le]; constructor<;> linarith [Hc.1,Hc.2]
  have hs': |cd0 v-pd v-bd0 v|≤1093/10000:=by
    rw [abs_le] at hpd h₃ Hd ⊢
    constructor<;>linarith [hpd.1,hpd.2,h₃.1,h₃.2,Hd.1,Hd.2]
  have hi:= sq_le_sq.mpr (le_trans hs (le_abs_self _))
  have hi':= sq_le_sq.mpr (le_trans hs' (le_abs_self _))
  change costs v<_
  unfold costs tmax lam; norm_num at hf hi hi' ⊢; linarith

lemma sCase2 (H:NG)(m h:ℝ)(hm:0 ≤ m)(he:left m h ≤ - (14/10)):
    costs (seg m h)<(1+tmax)*fstar h:=by
  let v:= seg m h;let x:=left m h;let y:=right m h
  have hH:14/10 ≤ h:= by unfold left at he;linarith
  have hh:0<h:=by linarith
  have hx:14/10 ≤ |x|:=by unfold x; linarith [neg_abs_le (left m h)]
  have hy:14/10 ≤ |y|:=by
    have hi:14/10 ≤ y:=by unfold y right;linarith
    linarith [le_abs_self y]
  have hkL (u:ℝ)(h:14/10≤ |u|): (-1)/10000 ≤ Kp (xs u)∧ Kp (xs u)≤191/10000 := hKe H u h
  have hcL (u:ℝ)(h:14/10≤ |u|): (-5010)/10000≤Cp (xs u)∧ Cp (xs u)≤-4950/10000 := hCe H u h
  obtain ⟨hkp,hk⟩:=hkL x hx
  obtain ⟨hcl,hc⟩:=hcL x hx
  obtain ⟨hf0,hf1⟩:=hkL y hy
  obtain ⟨hg,hg'⟩:=hcL y hy
  let e := Cp v.2-Cp v.1
  change _ ≤ Kp v.1 at hkp
  change Kp v.1 ≤_ at hk
  change _ ≤ Cp v.1 at hcl
  change Cp v.1 ≤_ at hc
  change _≤ Kp v.2 at hf0
  change Kp v.2≤_ at hf1
  change _≤ Cp v.2 at hg
  change Cp v.2≤ _ at hg'
  have hE : -(6/1000:ℝ) ≤ e ∧ e≤6/1000 := by unfold e; constructor<;>linarith
  obtain ⟨hf,hpa,hpb,hpd⟩:=arc11 m (show 11/10 ≤ h by linarith)
  have hi : Yval (Kp v.1) (Kp v.2) e ≤ (2/10000:ℝ):=
    Ybound _ _ _ _ _ _ _ _ _ _ hkp hk hf0 hf1 hE.1 hE.2 (by
      intro x hx y hy z hz; simp only [mem_insert_iff,mem_singleton_iff] at *
      rcases hx with hx|hx<;> rcases hy with hy|hy<;> rcases hz with hz|hz<;>
        rw [hx,hy,hz]<;> norm_num [Yval,mstar,tc,Profile.tr])
  have hg0:ek v+sgamma v≤277/10000:= by
    have hmv: bav Kp v≤275/10000:= (segR Kp testK hh.le _ _ (fun t _=>hK H t)).2
    rw [EK_eq]; change _+Yval _ _ e≤ _
    linarith
  obtain ⟨h₁,h₂,h₃⟩:= Psmall H m hh
  have ha: seg m h=v:=rfl
  rw [ha] at h₁ h₂ h₃
  obtain ⟨hz,hu,-⟩:= init_phase m h hh
  rw [ha] at hz hu
  rw [← hz] at hpa hpb; rw [← hu] at hpd
  have ht: -5010/10000 ≤ bav Cp v∧ bav Cp v ≤ -3410/10000 :=
    segR Cp testC hh.le _ _ (fun t _=>hC H t)
  have Hc : -(6/1000)≤ ca0 v∧ca0 v≤160/1000:=by
    unfold ca0; constructor<;> linarith [ht.1,ht.2]
  have Hd : |cd0 v|≤ 3/1000:=by
    change |e/2|≤_; rw [abs_le];constructor<;>linarith [hE.1,hE.2]
  have hs: |ca0 v-pa v-ba v|≤146/1000:=by rw [abs_le]; constructor<;> linarith [Hc.1,Hc.2]
  have hs': |cd0 v-pd v-bd0 v|≤323/10000:=by
    rw [abs_le] at hpd h₃ Hd ⊢
    constructor<;>linarith [hpd.1,hpd.2,h₃.1,h₃.2,Hd.1,Hd.2]
  have hi:= sq_le_sq.mpr (le_trans hs (le_abs_self _))
  have hi':= sq_le_sq.mpr (le_trans hs' (le_abs_self _))
  change costs v<_
  unfold costs tmax lam; norm_num at hf hi hi' ⊢; linarith
end GeneralMahler.SCal.SE

end

end OAI
