import OAI.Geometry.Convex.GeneralMahler.Scalar.LayerProof
import OAI.Geometry.Convex.GeneralMahler.Linear.Segments

namespace OAI
/-! §08 segment coordinates and physical averages. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.SCal.SE
open Tag Grid Profile Segment Jet
variable {m h:ℝ}
def left (m h :ℝ):=m-h
def right (m h:ℝ):=m+h
def seg (m h:ℝ):Plane:=(xs (left m h),xs (right m h))
def loc (m h β:ℝ):=m+h*β
def mean0 (f:ℝ→ℝ):=(1/2:ℝ)*(∫ β in (-1:ℝ)..1,f β)
def de (m h:ℝ)(x:ℝ):= cosh (loc m h x)
def normM (m h:ℝ):= mean0 (de m h)
def normE (m h:ℝ)(f:ℝ→ℝ):=mean0 (fun x=> de m h x*f x)/normM m h
def Pbar (m h:ℝ)(f:ℝ→ℝ):=normE m h (fun x=> f (loc m h x))

lemma mean_const (a:ℝ): mean0 (fun _=>a) = a:=by unfold mean0; rw [intervalIntegral.integral_const]; simp; ring
variable {f g:ℝ→ℝ}
lemma mean_add (hf:Continuous f)(hg:Continuous g):
    mean0 (fun x=> f x+g x)=mean0 f+mean0 g := by
  unfold mean0; rw [intervalIntegral.integral_add (hf.intervalIntegrable ..) (hg.intervalIntegrable ..)]
  ring
lemma mean_sub (hf:Continuous f)(hg:Continuous g):
    mean0 (fun x=> f x-g x)=mean0 f-mean0 g := by
  unfold mean0; rw [intervalIntegral.integral_sub (hf.intervalIntegrable ..) (hg.intervalIntegrable ..)]
  ring
lemma mean_scale (a:ℝ)(f:ℝ→ℝ):
    mean0 (fun x=>a*f x)=a*mean0 f:=by unfold mean0;rw [intervalIntegral.integral_const_mul];ring
lemma mean_mono (hf:Continuous f)(hg:Continuous g)(he:∀ x∈Icc (-1:ℝ) 1,f x ≤ g x):
    mean0 f ≤ mean0 g := by
  have hl : (-1:ℝ) ≤1:=by norm_num
  unfold mean0; exact mul_le_mul_of_nonneg_left
    (intervalIntegral.integral_mono_on hl (hf.intervalIntegrable ..) (hg.intervalIntegrable ..) he)
    (by norm_num)
lemma mean_ref (f:ℝ→ℝ):mean0 (fun x=>f (-x))=mean0 f:=by
  unfold mean0
  rw [intervalIntegral.integral_comp_neg]; simp

lemma cLoc (m h:ℝ):Continuous (loc m h):=continuous_const.add (continuous_const.mul continuous_id)
lemma cDe (m h:ℝ):Continuous (de m h):= continuous_cosh.comp (cLoc ..)
lemma normGe (m h:ℝ):1 ≤ normM m h := by
  have hi:=mean_mono continuous_const (cDe m h) (f:=fun _=>1) (fun y _=>Real.one_le_cosh _)
  rwa [mean_const] at hi
lemma normp (m h:ℝ):0 < normM m h:=lt_of_lt_of_le zero_lt_one (normGe ..)

lemma neScale (m h a:ℝ)(f:ℝ→ℝ):normE m h (fun x=>a*f x)=a*normE m h f:= by
  unfold normE; simp_rw [mul_left_comm (de ..)]
  rw [mean_scale]; ring
lemma neConst (m h a:ℝ): normE m h (fun _=>a) = a:= by
  unfold normE; simp_rw [mul_comm _ a]
  rw [mean_scale]; unfold normM
  have hp:=normp m h; unfold normM at hp; field_simp
lemma neMono (m h:ℝ)(hf:Continuous f)(hg:Continuous g)
    (he:∀ x∈Icc (-1:ℝ) 1,f x≤g x):
    normE m h f≤normE m h g:=by
  unfold normE
  apply div_le_div_of_nonneg_right _ (normp ..).le
  apply mean_mono ((cDe ..).mul hf) ((cDe ..).mul hg)
  exact fun x hx=> mul_le_mul_of_nonneg_left (he x hx) (Real.cosh_pos _).le
lemma neAdd (m h:ℝ)(hf:Continuous f)(hg:Continuous g):
    normE m h (fun x=>f x+g x)=normE m h f+normE m h g:=by
  unfold normE; simp only [mul_add]; rw [show mean0 _= mean0 _ + mean0 _ from mean_add (f:=fun x=>de m h x*f x) ((cDe m h).mul hf) (g:=fun x=>de m h x*g x) ((cDe m h).mul hg)]
  ring
lemma neSub (m h:ℝ)(hf:Continuous f)(hg:Continuous g):
    normE m h (fun x=>f x-g x)=normE m h f-normE m h g:=by
  unfold normE; simp only [mul_sub]; rw [show mean0 _= mean0 _ - mean0 _ from mean_sub (f:=fun x=>de m h x*f x) ((cDe m h).mul hf) (g:=fun x=>de m h x*g x) ((cDe m h).mul hg)]
  ring

lemma hsinh (m h:ℝ):sinh (m+h)-sinh (m-h)=2*cosh m*sinh h:=by
  rw [Real.sinh_add,Real.sinh_sub];ring
lemma loct (m h:ℝ)(x:ℝ): HasDerivAt (loc m h) h x:=by
  convert (((hasDerivAt_id' x).const_mul h).const_add m) using 1 <;> first| rfl| ring
lemma nor_eq (m h:ℝ) : h*normM m h=cosh m*sinh h:=by
  have he (x:ℝ):HasDerivAt (fun x=>sinh (loc m h x)) (h*de m h x) x:=by
    rw [mul_comm]; exact (Real.hasDerivAt_sinh _).comp x (loct ..)
  have ht:= intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _=>he x)
    ((continuous_const.mul (cDe ..)).intervalIntegrable (-1:ℝ) 1)
  rw [intervalIntegral.integral_const_mul,show loc m h 1=m+h from by unfold loc;ring,
    show loc m h (-1)=m-h from by unfold loc;ring,hsinh] at ht
  unfold normM mean0; linarith
lemma loch_local (m h:ℝ) (u:ℝ) (hh:0≤h) (he:u∈Icc (-1:ℝ) 1):
    loc m h u∈Icc (left m h) (right m h):=by
  unfold loc left right; constructor<;>nlinarith [he.1,he.2]

-- transfer any continuous f (on all ℝ)
lemma bav_phys (f:ℝ→ℝ)(hf:Continuous f)(a b:ℝ):
    (b-a)*bav f (a,b) = ∫ t in a..b,f t:=by
  let p:= fun c=> ∫ t in a..c,f t
  have hd(c:ℝ):HasDerivAt p (f c) c:= intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable ..) (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt
  have he(c:ℝ):HasDerivAt (along (a,b)) (b-a) c:=by
    convert ((((hasDerivAt_const c 1).sub (hasDerivAt_id' c)).mul_const a).fun_add ((hasDerivAt_id' c).mul_const b)) using 1
    all_goals first|rfl|ring
  have ha (c): HasDerivAt (p ∘ along (a,b)) ((b-a)*f (along (a,b) c)) c:=by rw [mul_comm]; exact (hd _).comp _ (he c)
  have hu:= intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=>ha t)
    ((continuous_const.mul (hf.comp (show Continuous (along (a,b)) from continuous_iff_continuousAt.mpr fun x=> (he _).continuousAt))).intervalIntegrable (0:ℝ) 1)
  rw [intervalIntegral.integral_const_mul] at hu
  unfold bav; convert hu using 1
  simp [p,along]

lemma normChange (m h:ℝ) (f:ℝ→ℝ)(hf:Continuous f):
    (seg m h).2-(seg m h).1 = 2*sb*h*normM m h ∧
    (((seg m h).2-(seg m h).1)*Pbar m h (liftF f) = ∫ t in (seg m h).1..(seg m h).2,f t) := by
  let x:=seg m h
  let d:=x.2-x.1
  have hl : d=2*sb*h*normM m h := by
    change sb*sinh (m+h)-sb*sinh (m-h)=_
    rw [mul_assoc (2*sb),nor_eq]
    linear_combination sb * hsinh m h
  refine ⟨hl,?_⟩
  let p:=fun c=>∫ t in x.1..c,f t
  let g:=fun z=> xs (loc m h z)
  have hd(c):HasDerivAt p (f c) c:= intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable ..) (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt
  let l:= fun z=>de m h z*f (g z)
  have hc(t): HasDerivAt g (sb*h*de m h t) t:=by
    convert (xD _).comp t (loct ..) using 1 <;> first|rfl|(unfold ast de;ring)
  have ht(t):HasDerivAt (p ∘ g) ((sb*h)*l t) t:=by
    convert (hd _).comp t (hc t) using 1; first|rfl|(unfold l;ring)
  have he:= intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=>ht t)
    ((continuous_const.mul (show Continuous l from (cDe ..).mul (hf.comp
      (continuous_iff_continuousAt.mpr fun x=>(hc _).continuousAt)))).intervalIntegrable (-1:ℝ) 1)
  rw [intervalIntegral.integral_const_mul] at he
  have h1:g 1=x.2:= by unfold g x loc seg right;rw [mul_one]
  have h2:g (-1)=x.1:=by unfold g x loc seg left;simp [sub_eq_add_neg]
  simp only [Function.comp_apply,h1,h2,p,intervalIntegral.integral_same,sub_zero] at he
  change d*((1/2*(∫ t in (-1:ℝ)..1,l t))/normM m h)=_
  rw [hl,← he]
  have hp:= normp m h; field_simp
lemma bav_norm (m h:ℝ)(f:ℝ→ℝ)(hf:Continuous f) :
    bav f (seg m h)=Pbar m h (liftF f):= by
  let x:=seg m h
  by_cases h0:h=0
  · subst h
    change bav f (xs _,xs _)=_
    simp only [left,right,sub_zero,add_zero,bav_same,Pbar,loc,zero_mul]
    apply Eq.symm (neConst m 0 (f _))
  have he := normChange m h f hf
  have hx : x.2-x.1 ≠0 := by
    rw [show x.2-x.1=_ from he.1]; have hp:= normp m h
    exact mul_ne_zero (mul_ne_zero (by have hh:=hsb; positivity) h0) hp.ne'
  apply mul_left_cancel₀ hx
  rw [show x=(x.1,x.2) from rfl]
  exact (bav_phys f hf x.1 x.2).trans he.2.symm
end GeneralMahler.SCal.SE

end

end OAI
