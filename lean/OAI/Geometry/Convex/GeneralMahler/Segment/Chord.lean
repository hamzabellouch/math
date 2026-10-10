import OAI.Geometry.Convex.GeneralMahler.Segment.Mean

namespace OAI
/-! §08 chord kernel W for signed comparison. -/
noncomputable section
open Set Filter Real MeasureTheory MeasureTheory.Measure
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.SCal.SE
open Profile Tag Jet
variable (m h:ℝ)
def leng:= (seg m h).2-(seg m h).1
def shv:= sinh h /h
def cθ (x:ℝ):=(xs (loc m h x)-(seg m h).1)/leng m h
def omega (x:ℝ):=6*cθ m h x*(1-cθ m h x)*cosh m/(de m h x)*shv h
lemma lnv (hh:0<h):0<leng m h:= sub_pos.mpr (x_mono (by unfold left right;linarith))
lemma θ_occ (hh:0<h)(x:ℝ)(hx:x∈Icc (-1:ℝ) 1): cθ m h x∈Icc (0:ℝ) 1:=by
  obtain ⟨hv,hz⟩:=loch_local m h x hh.le hx
  unfold cθ
  refine ⟨div_nonneg (sub_nonneg.mpr (x_mono.monotone hv)) (lnv m h hh).le,?_⟩
  rw [div_le_one (lnv m h hh)]
  exact sub_le_sub_right (x_mono.monotone hz) _
lemma om0 (hh:0<h)(x:ℝ)(hx:x∈Icc (-1:ℝ) 1):0≤ omega m h x:=by
  obtain ⟨ha,hb⟩:=θ_occ m h hh x hx
  have ht:0≤1-cθ m h x:=sub_nonneg.mpr hb
  have hp(x:ℝ):0<de m h x:=Real.cosh_pos _
  have hv:= Real.sinh_pos_iff.mpr hh
  unfold omega shv; have hq:=hp x; positivity

variable {f:ℝ→ℝ}
lemma cX0 (u v:ℝ) (hf:TestF f):
    let g:=fun y=> (y-u)*(v-y)*deriv (deriv f) y
    (∫ x in u..v,g x)= (v-u)*(f v+f u)-2*(∫ x in u..v,f x) := by
  intro g
  let p:=fun y=> (y-u)*(v-y)*deriv f y-(u+v-2*y)*f y-2*prim f y
  have he(y:ℝ): HasDerivAt p (g y) y:= by
    have hi:= ((((((hasDerivAt_id' y).sub_const u).mul ((hasDerivAt_id' y).const_sub v)).mul
      (hf.der.diff y).hasDerivAt).sub ((((hasDerivAt_id' y).const_mul 2).const_sub (u+v)).mul
      (hf.diff y).hasDerivAt)).sub ((prim_d hf y).const_mul 2))
    convert hi using 1
    all_goals first| rfl| (unfold g;simp only [Pi.mul_apply];ring)
  have hp:= intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _=>he x)
    ((show Continuous g from ((continuous_id.sub continuous_const).mul (continuous_const.sub continuous_id)).mul
      hf.der.der.cont).intervalIntegrable u v)
  have hh:= intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _=> prim_d hf x)
    (hf.cont.intervalIntegrable u v)
  rw [hp,hh]; unfold p;ring

lemma omCont: Continuous (omega m h):=by
  have hi:Continuous (cθ m h):=by unfold cθ loc xs; fun_prop
  have hh(x): de m h x≠0:= (cosh_pos _).ne'
  unfold omega
  have ha:Continuous (fun x=>6*cθ m h x*(1-cθ m h x)*cosh m):= (((continuous_const.mul hi).mul (continuous_const.sub hi)).mul continuous_const)
  exact (ha.div (cDe ..) hh).mul continuous_const
lemma ch_err (hh:0<h) (hf:TestF f):
    let v:=seg m h
    bav f v - (f v.1+f v.2)/2 =
      -(h^2/3)* mean0 (fun x=>omega m h x*NNf f (loc m h x)):= by
  intro v
  let u:=seg m h
  let g:=fun x=>(x-v.1)*(v.2-x)*deriv (deriv f) x
  have hg:Continuous g:= ((continuous_id.sub continuous_const).mul
    (continuous_const.sub continuous_id)).mul hf.der.der.cont
  have he (x:ℝ):
      de m h x*liftF g (loc m h x)=
        2*(h^2/3)*normM m h*(omega m h x*NNf f (loc m h x)) := by
    let t:= loc m h x
    rw [(SCov f hf (loc m h x)).1]
    have H := (normChange m h f hf.cont).1
    have ht : 0<normM m h:=normp ..
    have hp : 0<de m h x:=Real.cosh_pos _
    unfold omega cθ shv
    let a := de m h x
    have hu:0<leng m h :=lnv m h hh
    have hn:leng m h=2*sb*h* normM m h:=H
    change a*((xs t-v.1)*(v.2-xs t)*deriv (deriv f) (xs t))=
      2*_*_*(6*((xs t-v.1)/leng m h)*(1-(xs t-v.1)/leng m h)*cosh m /a* (sinh h/h)*
        ((sb*a)^2*deriv (deriv f) (xs t)))
    have hi : 1-(xs t-v.1)/leng m h = (v.2-xs t)/leng m h:=by
      field_simp
      change v.2-v.1-_=_
      ring
    rw [hi]
    have he : cosh m = h*normM m h/sinh h:=by
      rw [eq_div_iff (Real.sinh_pos_iff.mpr hh).ne']; exact (nor_eq ..).symm
    rw [hn,he]; have hsb:=hsb; have ht':=Real.sinh_pos_iff.mpr hh
    have hp':0<a:=hp
    field_simp; ring
  have hw:= (normChange m h g hg).2
  have hv:= bav_phys f hf.cont v.1 v.2
  change leng m h*Pbar m h (liftF g)=_ at hw
  unfold Pbar normE at hw; simp_rw [he,mean_scale] at hw
  have hc:= cX0 v.1 v.2 hf
  change (∫ x in v.1..v.2,g x)=_ at hc
  change leng m h*_ = ∫ x in v.1..v.2,g x at hw
  rw [← hw,← hv] at hc
  have hn:=normp m h
  let p:=mean0 fun x=>omega m h x*NNf f (loc m h x)
  change leng m h*(2*(h^2/3)*normM m h*p/normM m h)=
    leng m h*(f v.2+f v.1)-2*(leng m h*bav f v) at hc
  rw [show 2*(h^2/3)*normM m h*p/normM m h=2*(h^2/3)*p by field_simp] at hc
  apply mul_left_cancel₀ (lnv m h hh).ne'
  change leng m h*_ = leng m h*(-(h^2/3)*p)
  linarith
end GeneralMahler.SCal.SE

end

end OAI
