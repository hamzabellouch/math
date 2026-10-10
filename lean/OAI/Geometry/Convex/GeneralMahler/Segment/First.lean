import OAI.Geometry.Convex.GeneralMahler.Segment.Disp

namespace OAI
/-! Combine chord and endpoint variation using pointwise U star. -/
noncomputable section
open Set Filter Real MeasureTheory
open scoped Interval
namespace GeneralMahler.SCal.SE
open Tag Grid Profile Jet Segment
variable (m:ℝ){h:ℝ}
def alongD (m h:ℝ)(f:ℝ→ℝ):=fun x=> DotF f (loc m h x)
def alongN (m h:ℝ)(f:ℝ→ℝ):=fun x=> NNf f (loc m h x)
lemma hoD {f:ℝ→ℝ} (hf:TestF f) :
    anti (seg m h) f=2*h*mean0 (alongD m h f) := by
  let g:= (liftF f) ∘ (loc m h)
  have hd(x): HasDerivAt g (h*alongD m h f x) x:=by
    rw [mul_comm]; exact (liftD hf _).comp x (loct ..)
  have hc : Continuous (alongD m h f) := (Dt_cont hf).comp (cLoc ..)
  have hi:= intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=>hd t)
    ((continuous_const.mul hc).intervalIntegrable (-1:ℝ) 1)
  have he:g 1=f (seg m h).2:=by simp [g,Function.comp_apply,liftF,seg,right,loc]
  have hh:g (-1)=f (seg m h).1:=by simp [g,Function.comp_apply,liftF,seg,left,loc,sub_eq_add_neg]
  rw [intervalIntegral.integral_const_mul,he,hh] at hi
  unfold mean0 anti; linarith

def GammaB (f g:ℝ):=(12*(8/10:ℝ)/mstar^2)*(125/100*(f+tc*g)^2+5*Profile.tr^2*g^2)
lemma gmBound :
    sgamma (seg m h) ≤ h^2/3*mean0 (fun x=>GammaB (alongD m h Kp x) (alongD m h Cp x)):= by
  let f:=alongD m h Kp
  let g:=alongD m h Cp
  have hc:Continuous f:=(Dt_cont testK).comp (cLoc ..)
  have hd:Continuous g:=(Dt_cont testC).comp (cLoc ..)
  let l:=fun x:ℝ=>f x+tc*g x
  have hi:Continuous l:=hc.add (continuous_const.mul hd)
  have hm:mean0 l=mean0 f+tc*mean0 g:=by rw [show mean0 l= _ from mean_add hc
    (show Continuous (fun x=>tc*g x) from continuous_const.mul hd),mean_scale]
  let c:ℝ:=12*(8/10)/mstar^2
  let a:ℝ:=125/100;let b:=5*Profile.tr^2
  have he:=mean_cs hi; have hh:=mean_cs hd
  unfold sgamma
  rw [hoD m testK,hoD m testC]
  change _ ≤ h^2/3*mean0 (fun x=> c * (a * (l x)^2+b*(g x)^2))
  rw [mean_scale,mean_add (show Continuous (fun x=>a*(l x)^2) from continuous_const.mul (hi.pow _))
    (show Continuous (fun x=>b*(g x)^2) from continuous_const.mul (hd.pow _)),mean_scale,mean_scale]
  have hx : a*(mean0 l)^2+b*(mean0 g)^2 ≤ a*mean0 _+b*mean0 _:=
    add_le_add (mul_le_mul_of_nonneg_left he (by unfold a;norm_num))
      (mul_le_mul_of_nonneg_left hh (by unfold b;positivity))
  apply le_trans _ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx (by unfold c; positivity))
    (by positivity))
  rw [hm]; unfold c a b f g;apply le_of_eq;ring

def negN (m h:ℝ):= fun x=> -(omega m h x*alongN m h Kp x)
lemma ekB (hh:0<h):
    ek (seg m h)=h^2/3*mean0 (negN m h):=by
  have hi:=ch_err m h hh testK
  have he (f:ℝ→ℝ): mean0 (fun x=> -f x) = -mean0 f:=by
    unfold mean0;rw [intervalIntegral.integral_neg];ring
  unfold negN alongN ek
  have hEq := he (fun x=>omega m h x*NNf Kp (loc m h x))
  rw [hEq]
  dsimp only at hi
  linarith

lemma smallU (H:NG)(hh:0<h)(he:h≤16/100):
    ek (seg m h)+sgamma (seg m h) ≤ 54/100*ubase h := by
  let l:= fun x=>GammaB (alongD m h Kp x) (alongD m h Cp x)
  let S:=negN m h
  have hc:Continuous S:= ((omCont m h).mul ((nn_cont testK).comp (cLoc ..))).neg
  have hd: Continuous l:= by
    have he:Continuous (alongD m h Kp):=(Dt_cont testK).comp (cLoc ..)
    have hv:Continuous (alongD m h Cp):=(Dt_cont testC).comp (cLoc ..)
    unfold l GammaB;fun_prop
  have hp:=mean_mono (hc.add hd) continuous_const
    (f:=fun x=>S x+l x) (g:=fun _=>Ur) ?_
  · rw [mean_add hc hd, mean_const] at hp
    rw [ekB m hh]
    apply le_trans (add_le_add le_rfl (gmBound m)); rw [← mul_add]
    apply le_trans (mul_le_mul_of_nonneg_left hp (by positivity))
    unfold Ur ubase wp; apply le_of_eq;ring
  intro x hx
  let t:=loc m h x
  let D:=NNf Kp t
  have hi: 1507/1000*max 0 (-D)+l x≤Ur:= (GlobalCorr H t).2.2.2
  have hh:= (Wshr m hh he).1 x hx
  have hz :0 ≤ omega m h x := hh.1
  change -(omega m h x * D)+l x ≤ Ur
  apply le_trans _ hi
  apply add_le_add _ le_rfl
  rw [← mul_neg]
  calc
    _ ≤ omega m h x*max 0 (-D):=mul_le_mul_of_nonneg_left (le_max_right ..) hz
    _ ≤ _:=mul_le_mul_of_nonneg_right hh.2 (le_max_left ..)
lemma chAbs (hh:0<h)(he:h≤16/100) {f:ℝ→ℝ} (hf:TestF f){a:ℝ}
    (ha:0≤a) (hp:∀ x,|NNf f x| ≤ a):
    let v:=seg m h
    |bav f v-(f v.1+f v.2)/2| ≤h^2/3*((1012/1000:ℝ)*a) :=by
  intro v; rw [ch_err m h hh hf,abs_mul,abs_neg,abs_of_nonneg (by positivity)]
  let g:=fun x=>omega m h x*NNf f (loc m h x)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  change |mean0 g|≤_
  obtain ⟨he,hb⟩:=Wshr m hh he
  have hc:=omCont m h
  have hg:Continuous g:= hc.mul ((nn_cont hf).comp (cLoc ..))
  have hx(t:ℝ)(ht:t∈Icc (-1:ℝ) 1): -a*omega m h t≤g t ∧ g t≤a*omega m h t:=by
    obtain ⟨ha,hc⟩:=abs_le.mp (hp (loc m h t))
    have h' :=(he t ht).1
    unfold g; constructor<;>nlinarith
  have hh:= mean_mono (show Continuous (fun x=> -a*omega m h x) from continuous_const.mul hc) hg
    (fun t ht=>(hx t ht).1)
  have hj:= mean_mono hg (show Continuous (fun x=>a*omega m h x) from continuous_const.mul hc)
    (fun t ht=>(hx t ht).2)
  rw [mean_scale] at hh hj
  apply abs_le.mpr; constructor <;>nlinarith
end GeneralMahler.SCal.SE

end

end OAI
