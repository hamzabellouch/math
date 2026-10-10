import OAI.Geometry.Convex.GeneralMahler.Segment.Cost

namespace OAI
/-! Circular means on normalized interval and variance inequality. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology Interval
namespace GeneralMahler.SCal.SE
open Tag Grid Profile Segment Jet
variable (m h:ℝ)
def cott (h:ℝ):=Real.cosh h/Real.sinh h
local notation "w" => Profile.omegaP
def PhiA (h:ℝ):=(cos (w*h)+w*cott h*sin (w*h))/(1+w^2)
def PhiB (h:ℝ):=(cott h*sin (w*h)-w*cos (w*h))/(1+w^2)
def fstar (h:ℝ):= r^2/(1+w^2)*(w^2 - sin (w*h)^2/sinh h^2)
def Pastar (h:ℝ):= 2*r^2*(1-PhiA h*cos (w*h))
def Pdstar (m h:ℝ):= -2*r^2* PhiB h*tanh m*sin (w*h)

abbrev Fxc (m:ℝ)(t:ℝ):= Real.cos (w*(t-m))
abbrev Fxs (m:ℝ)(t:ℝ):= Real.sin (w*(t-m))
lemma dcx (t:ℝ): HasDerivAt (Fxc m) (-w*Fxs m t) t:= by
  convert ((((hasDerivAt_id' t).sub_const m).const_mul w).cos) using 1; first|rfl|(unfold Fxs;ring)
lemma dsx (t:ℝ): HasDerivAt (Fxs m) (w*Fxc m t) t:= by
  convert ((((hasDerivAt_id' t).sub_const m).const_mul w).sin) using 1; first|rfl|(unfold Fxc;ring)
lemma phaseAC (hh:0<h):
    Pbar m h (Fxc m)=PhiA h ∧ Pbar m h (Fxs m)=PhiB h*tanh m:=by
  let K:=1+w^2
  have hK:0<K:=by unfold K; positivity
  let C := Fxc m
  let S := Fxs m
  let F := fun t=> (sinh t*C t+w*cosh t*S t)
  let G := fun t=> (sinh t*S t-w*cosh t*C t)
  have hc (x):HasDerivAt F (K*cosh x*C x) x := by
    convert ((((Real.hasDerivAt_sinh x).mul (dcx m x)).add
      (((Real.hasDerivAt_cosh x).const_mul w).mul (dsx m x)))) using 1
    unfold C K; ring
  have hs (x):HasDerivAt G (K*cosh x*S x) x:= by
    convert ((((Real.hasDerivAt_sinh x).mul (dsx m x)).sub
      (((Real.hasDerivAt_cosh x).const_mul w).mul (dcx m x)))) using 1
    unfold S K; ring

  have hi (f g:ℝ→ℝ)(hf:Continuous f)(hg:∀ t:ℝ,HasDerivAt g (K*cosh t*f t) t):
      2*K*cosh m*sinh h*Pbar m h f=g (m+h)-g (m-h):= by
    let l:=fun t=>de m h t*f (loc m h t)
    have hu (t):HasDerivAt (g ∘ loc m h) ((K*h)*l t) t := by
      convert ((hg (loc m h t)).comp t (loct ..)) using 1
      all_goals first|rfl|(unfold l de;ring)
    have he:= intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=>hu t)
      ((continuous_const.mul ((cDe ..).mul (hf.comp (cLoc ..)))).intervalIntegrable (-1:ℝ) 1)
    have h₁:loc m h 1=m+h:=by unfold loc;ring
    have h₂:loc m h (-1)=m-h:=by unfold loc;ring
    rw [intervalIntegral.integral_const_mul] at he
    simp only [Function.comp_apply,h₁,h₂] at he
    have hp : 0< normM m h:=normp ..
    rw [← he]; change 2*K*cosh m*sinh h*(1/2*(∫ t in (-1:ℝ)..1,l t)/normM m h)=_
    rw [show 2*K*cosh m*sinh h=2*K*(h*normM m h) by rw [nor_eq];ring]
    field_simp
  let c:= Real.cos (w*h)
  let s:= Real.sin (w*h)
  have h₁:C (m+h)=c:= by unfold C Fxc; congr 2; ring
  have h₂:S (m+h)=s:= by unfold S Fxs; congr 2; ring
  have h₃:C (m-h)=c:=by unfold C Fxc; rw [show w*(m-h-m)= -(w*h) by ring,cos_neg]
  have h₄:S (m-h)= -s:=by unfold S Fxs; rw [show w*(m-h-m)= -(w*h) by ring,sin_neg]
  have hc₀:Continuous C:= continuous_iff_continuousAt.mpr fun t=>(dcx ..).continuousAt
  have hs₀:Continuous S:= continuous_iff_continuousAt.mpr fun t=>(dsx ..).continuousAt
  have hj:= Real.sinh_pos_iff.mpr hh
  have hm:=Real.cosh_pos m
  have h0 : 2*K*cosh m*sinh h ≠ 0:=by positivity
  constructor
  · change Pbar m h C=_
    apply mul_left_cancel₀ h0; rw [hi C F hc₀ hc]
    unfold F; rw [h₁,h₂,h₃,h₄,sinh_add,sinh_sub,cosh_add,cosh_sub]
    unfold PhiA cott c s; change _=2*K*cosh m*sinh h*(_/K)
    field_simp; ring
  change Pbar m h S=_
  apply mul_left_cancel₀ h0; rw [hi S G hs₀ hs]
  unfold G; rw [h₁,h₂,h₃,h₄,sinh_add,sinh_sub,cosh_add,cosh_sub]
  unfold PhiB cott c s; rw [Real.tanh_eq_sinh_div_cosh]
  change _=2*K*cosh m*sinh h*(_/K*_)
  field_simp; ring

lemma lc_rot (x y:ℝ): lc (x+y)=lc x*cos (w*y)-ls x*sin (w*y):=by
  rw [lc_e,lc_e,ls_e,mul_add,cos_add]; ring
lemma ls_rot (x y:ℝ): ls (x+y)=ls x*cos (w*y)+lc x*sin (w*y):=by
  rw [ls_e,lc_e,ls_e,mul_add,sin_add];ring
lemma bcirc (hh:0<h):
    bav uc (seg m h)= lc m*PhiA h-ls m*(PhiB h*tanh m) ∧
    bav us (seg m h)= ls m*PhiA h+lc m*(PhiB h*tanh m) := by
  obtain ⟨hc,hs⟩:=phaseAC m h hh
  have he : lc=fun x=> lc m*Fxc m x-ls m*Fxs m x:= by
    funext x
    have hi:=lc_rot m (x-m); rw [add_sub_cancel] at hi; exact hi
  have he':ls=fun x=> ls m*Fxc m x+lc m*Fxs m x:= by
    funext x; have hi:=ls_rot m (x-m);rw [add_sub_cancel] at hi;exact hi
  have hC (x:ℝ): Continuous (fun t=>x * Fxc m (loc m h t)):= by unfold Fxc loc; fun_prop
  have hS(x:ℝ):Continuous (fun t=>x * Fxs m (loc m h t)):=by unfold Fxs loc; fun_prop
  rw [bav_norm _ _ _ ucs_reg.1.cont,bav_norm _ _ _ ucs_reg.2.cont]; rw [← hc,← hs]
  change Pbar m h lc=_ ∧ Pbar m h ls=_
  constructor
  · conv_lhs=>rw [he]
    unfold Pbar; rw [neSub m h (hC _) (hS _),neScale,neScale]
  conv_lhs=>rw [he']
  unfold Pbar; rw [neAdd m h (hC _) (hS _),neScale,neScale]
lemma PSum (x:Plane): sqav uc x + sqav us x=r^2:=by
  unfold sqav; rw [← bav_add (sq_test ucs_reg.1) (sq_test ucs_reg.2)]
  have hh : (fun x=> uc x^2+us x^2)=fun _=> r^2:=by
    ext x; obtain ⟨t,rfl⟩:=ontoX x; exact lcsq t
  rw [hh,bav_const]

lemma init_phase (hh:0<h) :
    let v:=seg m h
    pa v=Pastar h∧pd v=Pdstar m h∧vdis uc v+vdis us v ≥ fstar h := by
  intro v
  let a:=PhiA h; let b:=PhiB h
  let c:=cos (w*h); let s:=sin (w*h)
  have he:c^2+s^2=1 := by rw [add_comm]; exact Real.sin_sq_add_cos_sq _
  have hp:0<sinh h := Real.sinh_pos_iff.mpr hh
  have hv:a^2+b^2=(1+s^2/sinh h^2)/(1+w^2):=by
    have hj:= Real.cosh_sq_sub_sinh_sq h
    have h1 : 0<1+w^2 := by positivity
    unfold a b PhiA PhiB cott
    change ((c+_ * s)/_)^2+((_*s-_ * c)/_)^2=_
    field_simp
    linear_combination ((1+w^2)*sinh h^2)*he + ((1+w^2)*s^2)*hj
  have hx :=bcirc m h hh
  unfold pa pd pPlus vdis mdis
  have hw : v.2=xs (m+h):=rfl
  have hy : v.swap.2=xs (m-h):=rfl
  rw [bav_sym ucs_reg.1 v,bav_sym ucs_reg.2 v]; simp_rw [hw,hy]
  rw [show bav uc v=_ from hx.1,show bav us v=_ from hx.2]
  have h₁:=PSum v; have h₂:=PSum v.swap; have h₃:= lcsq m
  let u:=lc m; let t:=ls m
  have h₄: uc (xs (m+h))=u*c-t*s:=lc_rot m h
  have h₅: us (xs (m+h))=t*c+u*s:=ls_rot m h
  have h₆:uc (xs (m-h))=u*c+t*s:=by
    change lc (m-h)=_; rw [sub_eq_add_neg (b:=h),lc_rot]; simp [u,t,c,s]
  have h₇:us (xs (m-h))=t*c-u*s:=by
    change ls (m-h)=_; rw [sub_eq_add_neg (b:=h),ls_rot]; simp [u,t,c,s,sub_eq_add_neg]
  rw [h₄,h₅,h₆,h₇]
  have ha := Real.cos_sq_add_sin_sq (w*h)
  have ht: (Real.tanh m)^2 ≤1 := by rw [← th_eq]; exact (ri0 m).2
  unfold Pastar Pdstar fstar
  change u^2+t^2=r^2 at h₃
  rw [show sqav uc v=r^2-sqav us v by linarith,
    show sqav uc v.swap=r^2-sqav us v.swap by linarith]
  rw [← h₃]
  unfold u t c s a b at *
  refine ⟨?_,?_,?_⟩
  · linear_combination (lc m^2+ls m^2)*he
  · ring
  have he': w^2-sin (w*h)^2/sinh h^2 = (1+w^2)*(1-(PhiA h^2+PhiB h^2)) := by
    rw [hv]; field_simp; ring
  rw [he']
  have hP := mul_nonneg (show 0 ≤ lc m^2+ls m^2 from by positivity)
    (mul_nonneg (sq_nonneg (PhiB h)) (show 0 ≤ 1-tanh m^2 from by linarith))
  unfold Profile.omegaP at *; norm_num at *; nlinarith
end GeneralMahler.SCal.SE

end

end OAI
