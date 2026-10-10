import OAI.Geometry.Convex.GeneralMahler.Scalar.LayerAlg
import OAI.Geometry.Convex.GeneralMahler.Scalar.Universal

namespace OAI
/-! Pointwise scalar covariance and layer inequalities. -/
open Set Filter Real
namespace GeneralMahler.SCal
open Grid Tag Profile Cert Cert.IV Jet
variable (h:NG)
lemma SQrange (h:NG) (x:ℝ):113/1000≤ N2 qu x ∧ N2 qu x≤514/1000 := by
  obtain ⟨t,ht⟩:=ontoX x
  have hi:=mRange h t S
  rw [rng,mem_band] at hi
  simp only [Tag.act,liftF] at hi; rw [ht] at hi
  norm_num at *; exact hi
lemma Qrange (h:NG) (x:ℝ):775/10000≤ qu x∧qu x≤ 2559/10000:= by
  obtain ⟨t,ht⟩:=ontoX x
  have hi:=mRange h t Q; rw [rng,mem_band] at hi
  simp only [Tag.act,liftF] at hi; rw [ht] at hi
  norm_num at *; exact hi

-- choose one rectangle for each parameter
lemma onPanels (h:NG) (t:ℝ) :
    ∃ k:ℕ,k≤8 ∧ SIn (fun i=>i.act t) (panel k) ∧
      ro2 t≤ rPanel k^2 := by
  obtain ⟨n,_,hn,_,hb,hc⟩:= Propagate h (r:=0) (by decide)
    (show nd 0≤ |t| from nd0.symm ▸ abs_nonneg t)
  have hk:= (stage_size n hn).1
  refine ⟨stage n,hk,?_,rp_val _ hk _ hb⟩
  have he:=hc.pn
  rcases le_total 0 t with ht|ht
  · simpa only [abs_of_nonneg ht] using he
  rw [abs_of_nonpos ht] at he
  have hh (i:Tag)(he:i.odd=false):i.act (-t)=i.act t:=Tag.TvEv (hqt h) he t
  unfold SIn at *; dsimp only at *
  rwa [hh S (by rfl),hh Q (by rfl),hh V (by rfl)] at he

lemma Sp_upper (h:NG) (x:ℝ):N2 uc x^2+N2 us x^2 ≤ (1104/1000:ℝ)^2:=by
  obtain ⟨t,ht⟩:=ontoX x
  obtain ⟨k,hk,_,hr⟩:=onPanels h t
  rw [← ht,← nr2]
  apply hr.trans
  interval_cases k <;> norm_num [rPanel,panel,pan]
lemma CSr (a b x y c d:ℝ) (h:0≤ c)(he:0≤ d)(hh:a^2+b^2≤c^2)(hj:x^2+y^2≤d^2):
    |a*x+b*y|≤c*d:= by
  have hh': (a*x+b*y)^2≤(c*d)^2:= by
    rw [mul_pow]; apply le_trans _ (mul_le_mul hh hj (by positivity) (by positivity))
    nlinarith [sq_nonneg (a*y-b*x)]
  have hi:=sq_le_sq.mp hh'; rwa [abs_of_nonneg (mul_nonneg h he)] at hi
lemma kk_bd: 48/100 ≤ kk ∧ kk ≤ 49/100:= by
  have hp:=k_pos; have hh:=k_sq; unfold bb cc at hh; constructor <;> nlinarith
lemma h_contact (h:NG) (x y:ℝ): 0<4*cc+2*kk*(N2 qu x+N2 qu y)- N2 qu x*N2 qu y -
    (N2 uc x*N2 uc y+N2 us x*N2 us y) := by
  obtain ⟨ha,hb⟩:=SQrange h x; obtain ⟨hc,hd⟩:=SQrange h y
  have he:= le_of_abs_le (CSr _ _ _ _ _ _ (by norm_num) (by norm_num)
    (Sp_upper h x) (Sp_upper h y))
  have hi : 0≤ N2 qu x:= by linarith
  have hj : 0≤ N2 qu y:= by linarith
  have hf := mul_le_mul hb hd hj (show (0:ℝ)≤514/1000 by norm_num)
  have hu:= kk_bd.1
  unfold cc at *
  nlinarith

namespace PA
lemma kstats (k:Nat)(h:k≤8) : (panel k).sr ≠ unk ∧
    (panel k).qR≠ unk∧(panel k).vR≠ unk ∧
    eR true (panel k).sr ≤514/1000∧eR true (panel k).qR ≤256/1000 := by
  interval_cases k <;> norm_num [panel,pan,eR,w,endp,band,bandD,den]

lemma hMono {a b c d:ℝ} (ha:a ≤ b)(hb:c ≤ d)(he:d ≤514/1000)
    (hh:b ≤ 256/1000): HV a c≤HV b d:= by
  have hi:=kk_bd.1
  unfold HV
  have hp:= mul_nonneg (sub_nonneg.mpr ha) (show 0≤ 4*kk-2*c by linarith)
  have hv:=mul_nonneg (sub_nonneg.mpr hb) (show 0≤kk-b by linarith)
  nlinarith
end PA

open PA
lemma layer_line (h:NG) (t u:ℝ) :
    let v := (xs t,xs u)
    HH v + tc*Hh v-1/2*Profile.tr*(h₀+Hh v^2/h₀)>
      2*(bb+eta+(bb+eta-kar)*tmin)+2*bm*N2 qu v.1*N2 qu v.2+2*e₀*(2*Profile.tr)^2+Hh v^2/alpha := by
  intro v
  obtain ⟨kx,hkx,ha,hax⟩:=onPanels h u
  obtain ⟨kz,hkz,hb,hbx⟩:=onPanels h t
  let c := N2 qu (xs t)
  let d := N2 qu (xs u)
  let a:= qu (xs u)
  let w:= deriv (deriv Profile.v) (xs u)
  have hp (k) (h:k≤8): 0≤rPanel k:= rp_pos k h
  have kkx := kstats kx hkx; have kkz:= kstats kz hkz
  obtain ⟨hxq,hxs,hxv⟩:=ha
  obtain ⟨hzq,hzs,hzv⟩:=hb
  have Hxq:=orderE hxq kkx.2.1;have Hxs:= orderE hxs kkx.1
  have Hz:= orderE hzs kkz.1; have HV':= orderE hxv kkx.2.2.1
  change eR _ _≤ a ∧ a≤ _ at Hxq
  change eR _ _≤ c ∧ c≤ _ at Hz
  change eR _ _≤ d ∧ d≤ _ at Hxs
  let sd:= N2 uc (xs t)*uc (xs u)+N2 us (xs t)*us (xs u)
  have hR : 0 ≤ Profile.r:=by norm_num [r]
  have hj : |sd| ≤ rPanel kz*r := CSr _ _ _ _ _ _ (hp _ hkz) hR
    (by rw [← nr2];exact hbx)
    (le_of_eq (lcsq u))
  have heq : HH v= HV a c -2*sd := by unfold HH HV; rfl
  have hd : HH v∈Icc (Hbnd false kx kz) (Hbnd true kx kz):=by
    rw [heq]
    have hi := hMono Hxq.1 Hz.1 (Hz.2.trans kkz.2.2.2.1) (Hxq.2.trans kkx.2.2.2.2)
    have hv:= hMono Hxq.2 Hz.2 kkz.2.2.2.1 kkx.2.2.2.2
    unfold Hbnd; simp only [Bool.false_eq_true,ite_false,ite_true]
    have hg:=abs_le.mp hj; constructor <;> nlinarith [hg.1,hg.2]
  have hc : 0≤ c:= by have hj:=SQrange h (xs t);unfold c;linarith [hj.1]
  have H : 0≤ d := by have hj:=SQrange h (xs u);unfold d;linarith [hj.1]
  have h' := mul_le_mul Hxs.2 Hz.2 hc (H.trans Hxs.2)
  have hh:= whole hkx hkz (HH v) w hd HV'
  have hi : Lcost c d ≤ Lcost (eR true (panel kx).sr) (eR true (panel kz).sr):= by
    unfold Lcost
    have hp : 0≤2*bm := by norm_num [bm,bb,tmin,tmax,cc,eta]
    nlinarith
  have hv:=hi.trans_lt hh
  unfold Lcost Ldef at hv
  have he : Hh v= HH v+w-2*kar:=rfl
  change HH v + tc*_ -_ > _+2*bm*c*d+_+_
  rw [he]; unfold tc kar Profile.tr alpha h₀ at *; norm_num at *; linarith

theorem hSeg01 (h:NG): LayerOK := by
  refine ⟨hrq h,hqt h,ucs_reg.1,ucs_reg.2,Qeven,
    fun x=> ?_,fun x=>?_,h_contact h,?_⟩
  · linarith [(SQrange h x).1]
  · obtain ⟨t,ht⟩:=ontoX x
    have hi:= mRange h t RV
    rw [rng,mem_band] at hi
    simp only [Tag.act,liftF] at hi
    rw [ht] at hi
    norm_num at hi; apply abs_le.mpr; constructor <;> linarith [hi.1,hi.2]
  rintro ⟨x,z⟩
  obtain ⟨t,rfl⟩:=ontoX x; obtain ⟨u,rfl⟩:=ontoX z
  exact layer_line h t u

theorem upd_ok (h:NG): UpdatesOK Cp Kp := by
  refine ⟨testC.poly,testK.poly,testC.cont,testK.cont,?_,?_,?_,?_⟩
  all_goals intro x; obtain ⟨t,rfl⟩:=ontoX x; obtain ⟨ha,hb,hc,-⟩:= GlobalCorr h t
  · exact ha.le
  · exact hb.le
  · simp only [Tag.act,liftF,Ta] at hc; linarith
  have hi:= mRange h t C
  rw [rng,mem_band] at hi; simp only [Tag.act,liftF] at hi
  unfold cupper; norm_num at *; exact hi.2
end GeneralMahler.SCal

end OAI
