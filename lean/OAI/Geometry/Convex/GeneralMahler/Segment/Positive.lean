import OAI.Geometry.Convex.GeneralMahler.Segment.Distant

namespace OAI
/-! §08 both endpoints on positive tail. -/
noncomputable section
open Set Filter Real MeasureTheory
namespace GeneralMahler.SCal.SE
open Tag Grid Profile Jet Segment
variable (H:NG)(m:ℝ){h:ℝ}

lemma sf_base_small (hh:16/100 ≤ h)(he:h ≤3/10):
    (8/1000) ≤ fstar h ∧ (250/1000)*h^2 ≤fstar h:=by
  have hp:0 < h:=by linarith
  let x:=h^2
  have ha: (16/100:ℝ)^2≤ x:=by unfold x;gcongr
  have hb:x≤ (3/10:ℝ)^2:=by unfold x;gcongr
  let f:=ubase h*qsmall h
  have hc:=sfL hp
  unfold ubase qsmall wp at *
  constructor
  · apply le_trans _ hc
    rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
    unfold Profile.r Profile.omegaP at *
    norm_num
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  apply le_trans _ hc
  rw [← mul_div_assoc,le_div_iff₀ (by positivity)]
  have hh:= mul_le_mul_of_nonneg_left hb (sq_nonneg h)
  unfold x Profile.r Profile.omegaP at *;norm_num;nlinarith

lemma manyP (m h:ℝ)(hh:16/100 ≤ h):
    8/1000≤ fstar h ∧
      Pastar h+|Pdstar m h|≤ (150/1000) ∧
      Pastar h+|Pdstar m h|≤ (665/100)*fstar h:=by
  have hp:0<h:=by linarith
  rcases le_total h (3/10) with hx|hx
  · obtain ⟨h1,h2⟩:=sf_base_small hh hx
    have hQ : Pastar h=pa (seg m h):=(init_phase m h hp).1.symm
    have he: Pastar h ≤wp*h^2*(4/3+ (5/100)*h^2):= by rw [hQ]; exact (pa_short m hp hx).2
    have hz:=smallD m hp
    have hk:h^2 ≤ (3/10:ℝ)^2:=by gcongr
    have hl:=mul_le_mul_of_nonneg_left hx (sq_nonneg h)
    have hi:=mul_le_mul_of_nonneg_left hk (sq_nonneg h)
    unfold ubase wp Profile.r Profile.omegaP at *
    norm_num at *
    refine ⟨h1,?_,?_⟩ <;> nlinarith
  obtain ⟨h₁,h₂⟩:= arc30 m hx
  refine ⟨by linarith,h₂,?_⟩;linarith

lemma GammaTail (H:NG)(m h:ℝ)(hm:14/10≤ left m h)(hh:16/100 ≤ h):
    sgamma (seg m h) ≤(1/10)*fstar h:=by
  let x:=left m h; let y:=right m h
  have he:x≤y:=by unfold x y left right;linarith
  have hl:y-x=2*h:=by unfold x y left right;ring
  let a:=anti (seg m h) Kp; let b:=anti (seg m h) Cp
  rcases le_total h (4/10) with hR|hR
  · have hA(t:ℝ)(ht:t∈Icc x y):14/10 ≤|t|:= (hm.trans ht.1).trans (le_abs_self _)
    have hp : |a|≤ (211/10000)*(2*h):=by
      rw [← hl]; exact dist_bdd testK _ he
        (fun t ht=> abs_le.mpr (by simpa only [neg_div] using (hdKe H t (hA t ht))))
    have hc : |b| ≤ (84/10000)*(2*h):=by
      rw [← hl]; exact dist_bdd testC _ he
        (fun t ht=> abs_le.mpr (by simpa only [neg_div] using (hdCe H t (hA t ht))))
    have ht : 0<h:=by linarith
    have hL : (18/100:ℝ)*h^2≤fstar h:=by
      apply le_trans _ (sfL ht)
      unfold ubase wp qsmall
      rw [← mul_div_assoc,le_div_iff₀ (by positivity)]
      have he : h^2 ≤ (4/10:ℝ)^2:=by gcongr
      unfold r Profile.omegaP at *;norm_num; nlinarith [mul_le_mul_of_nonneg_left he (sq_nonneg h)]
    have hb:|a+tc*b|≤ ((211/10000)+tc*(84/10000))*(2*h):=by
      apply (abs_add_le ..).trans
      rw [abs_mul,abs_of_nonneg (show 0≤tc by norm_num [tc])]
      unfold tc at *; linarith
    change _*(125/100*(a+tc*b)^2+_*b^2)≤_
    have hi:= sq_le_sq.mpr (hb.trans (le_abs_self _)); have hu:=sq_le_sq.mpr (hc.trans (le_abs_self _))
    unfold tc mstar Profile.tr at *;norm_num at *; nlinarith
  have hp:410/1000 ≤ sinh h:=by
    apply le_trans _ (sinh_le_sinh.mpr hR)
    have hp:=sh3 (4/10) (by norm_num); linarith
  have hf:= fbase (show 0<h by linarith) _ (by norm_num) hp
  have hx:=hm.trans (le_abs_self _)
  have hy :14/10 ≤|y|:= (hm.trans he).trans (le_abs_self _)
  have ha:|a|≤ 192/10000 := by
    obtain ⟨h1,h2⟩:= hKe H x hx; obtain ⟨h3,h4⟩:= hKe H y hy
    change |Kp (xs y)-Kp (xs x)|≤ _
    rw [abs_le]; constructor<;>linarith
  have hb:|b|≤6/1000:=by
    obtain ⟨h1,h2⟩:= hCe H x hx;obtain ⟨h3,h4⟩:=hCe H y hy
    change |Cp (xs y)-Cp (xs x)|≤ _
    rw [abs_le]; constructor<;>linarith
  have hA:|a+tc*b|≤192/10000+tc*(6/1000):=by
    apply (abs_add_le ..).trans
    rw [abs_mul,abs_of_nonneg (show 0≤tc by norm_num [tc])]
    unfold tc; linarith
  have hi:=sq_le_sq.mpr (hA.trans (le_abs_self _));have hu:= sq_le_sq.mpr (hb.trans (le_abs_self _))
  change _*(125/100*(a+tc*b)^2+_*b^2)≤_
  unfold tc mstar Profile.tr Profile.r Profile.omegaP at *
  norm_num at *; nlinarith

lemma ekNeg (H:NG)(m h:ℝ)(he:14/10≤left m h)(hh:0<h):
    ek (seg m h) ≤ 0 := by
  rw [ekB m hh]
  have hi : mean0 (negN m h) ≤ mean0 (fun x=>0) :=by
    refine mean_mono ?_ continuous_const ?_
    · change Continuous fun x=> -(omega m h x*NNf Kp (loc m h x))
      exact ((omCont ..).mul ((nn_cont testK).comp (cLoc ..))).neg
    intro x hx
    change -(omega m h x*NNf Kp (loc m h x))≤ (0:ℝ)
    rw [neg_nonpos]
    have hv : 14/10 ≤|loc m h x| := (he.trans (loch_local m h x hh.le hx).1).trans (le_abs_self _)
    apply mul_nonneg (om0 m h hh x hx)
    have hj:=hNKe H (loc m h x) hv
    linarith [hj.1]
  rw [mean_const] at hi
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hi

lemma pplusNN (v:Plane):0≤pPlus v :=by
  have hp (f:ℝ→ℝ)(hf:TestF f):0 ≤ mdis f v:=by
    rw [mdis_eq hf]
    unfold bav; apply intervalIntegral.integral_nonneg
    · norm_num
    intro x _;exact sq_nonneg _
  exact add_nonneg (hp _ ucs_reg.1) (hp _ ucs_reg.2)

lemma costPos (H:NG)(m h:ℝ)(hm:14/10≤left m h)(hh:16/100 ≤h):
    costs (seg m h)<(1+tmax)*fstar h:=by
  let v:=seg m h
  let f:=fstar h
  have hH:0<h:=by linarith
  obtain ⟨hf,hp,hq⟩:=manyP m h hh
  obtain ⟨ha,hb,-⟩:=init_phase m h hH
  change pa v=_ at ha;change pd v=_ at hb
  rw [← ha, ← hb] at hp hq
  have hj:=ekNeg H m h hm hH
  have hv:=GammaTail H m h hm hh
  let I:= Icc (left m h) (right m h)
  have hI(t:ℝ)(ht:t∈I):14/10 ≤ |t|:= (hm.trans ht.1).trans (le_abs_self _)
  let a:ℝ:=(-5010)/10000;let b:ℝ:=(-4950)/10000
  have ht(t:ℝ)(ht:t∈I): Cp (xs t)∈Icc a b:=hCe H t (hI t ht)
  have ht1:bav Cp v∈Icc a b:=segR Cp testC hH.le _ _ ht
  have heq:left m h ≤ right m h:=by unfold left right; linarith
  have hl:Cp v.1∈Icc a b:=ht _ ⟨le_rfl,heq⟩
  have hr:Cp v.2∈Icc a b:=ht _ ⟨heq,le_rfl⟩
  obtain ⟨ht3,ht4⟩:= plusR H (m:=m) hH.le _ _ (fun x hx=>hQe H x (hI x hx))
  let g:ℝ:=45/100000
  have hP:qPlus v∈Icc 0 g:= by unfold g;norm_num at *; constructor;exact ht3.1;linarith [ht3.2]
  have hR:qPlus v.swap∈Icc 0 g:=by unfold g;norm_num at *;constructor;exact ht4.1;linarith [ht4.2]
  let M:=sqrt f
  have hf':f≥ 8/1000:=hf
  have he:M^2=f:=Real.sq_sqrt (by linarith)
  have hM:0≤M:=Real.sqrt_nonneg _
  have h₀: pa v+pd v=pPlus v ∧ pa v-pd v=pPlus v.swap:=by unfold pa pd;constructor<;>ring
  have h1(p:ℝ)(he0:0≤p)(hp0:p≤pa v+|pd v|):p≤ M := by
    have hs':= hp0.trans hp
    have ht':= hp0.trans hq
    change p ≤ _*f at ht'
    have hi:=mul_le_mul hs' ht' he0 (show 0≤ (150/1000:ℝ) by positivity)
    nlinarith
  have hps:=h1 _ (pplusNN v) (by rw [← h₀.1];linarith [le_abs_self (pd v)])
  have hpd:=h1 _ (pplusNN v.swap) (by rw [← h₀.2];linarith [neg_abs_le (pd v)])
  set A:=ca0 v-pa v-ba v
  set B:=cd0 v-pd v-bd0 v
  have hx : A+B=bav Cp v-Cp v.1-pPlus v-qPlus v:=by unfold A B ca0 cd0 pa ba pd bd0;ring
  have hx': A-B=bav Cp v-Cp v.2-pPlus v.swap-qPlus v.swap:=by unfold A B ca0 cd0 pa ba pd bd0;ring
  let z:ℝ:=645/100000
  have hh : |A+B|≤ M+z:= by
    rw [hx,abs_le];unfold a b g z at *
    constructor <;> linarith [pplusNN v,ht1.1,ht1.2,hl.1,hl.2,hP.1,hP.2]
  have hh' : |A-B|≤ M+z:= by
    rw [hx',abs_le]; unfold a b g z at *
    constructor<;> linarith [pplusNN v.swap,ht1.1,ht1.2,hr.1,hr.2,hR.1,hR.2]
  have HU: A^2+B^2≤(12/10:ℝ)*f:=by
    have hu:=sq_le_sq.mpr (hh.trans (le_abs_self _))
    have hi:=sq_le_sq.mpr (hh'.trans (le_abs_self _))
    have he': z ≤ (8/100:ℝ)* M:= by unfold z;nlinarith
    unfold z at *
    nlinarith
  have hpaBound : pa v+ba v ≤ (671/100:ℝ)*f := by
    have h:bav qu v=bav qu v:=rfl
    have hl: qPlus v≤g:=hP.2
    have ht: qPlus v.swap ≤ g:=hR.2
    have hj:ba v≤g := (div_le_div_of_nonneg_right (add_le_add hl ht) (show (0:ℝ)≤ 2 by norm_num)).trans_eq (show (g+g)/2=g by ring)
    unfold g f at *; linarith [_root_.abs_nonneg (pd v)]
  change costs v <(1+tmax)*f
  change _+_+(A^2+B^2)/(4*lam)+_ < _
  change ek v≤ _ at hj;change sgamma v ≤_*f at hv
  unfold tmax lam
  norm_num at HU hpaBound hj hv hf' ⊢
  linarith only [HU,hpaBound,hj,hv,hf']
end GeneralMahler.SCal.SE

end

end OAI
