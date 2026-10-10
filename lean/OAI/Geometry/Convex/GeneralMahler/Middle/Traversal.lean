import OAI.Geometry.Convex.GeneralMahler.Middle.Bound2

namespace OAI
/-! Uniform second derivative bound of endpoint spectral averages for smooth profiles. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric
open scoped Topology Interval
namespace GeneralMahler.SCal.Mid
open Tag Grid Jet Profile Segment SE
-- integral parametrization
variable {f g:ℝ→ℝ→ℝ}
def ment (f:ℝ→ℝ→ℝ) (x:ℝ):=mean0 (f x)
def contB (f:ℝ→ℝ→ℝ):=Continuous f.uncurry

lemma cmCont (hf:contB f): Continuous (ment f):= by
  have hi:= intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f:=f) (μ:=volume) hf (-1:ℝ) 1
  unfold ment mean0; exact continuous_const.mul hi

lemma curC (hf:contB f) (x:ℝ):Continuous (f x):=
  by
    let r:ℝ→ℝ×ℝ:=fun y=>(x,y)
    have h:Continuous r:= continuous_const.prodMk continuous_id
    exact (show Continuous (Function.uncurry f) from hf).comp h
lemma fmd (hf:contB f)(hg:contB g)(he:∀ x t,HasDerivAt (fun x=>f x t) (g x t) x)(x:ℝ):
    HasDerivAt (ment f) (ment g x) x := by
  let A:=Icc (x-1) (x+1)
  let B:=Icc (-1:ℝ) 1
  have hi:IsCompact (A ×ˢ B):= (isCompact_Icc).prod isCompact_Icc
  let w:= fun t:ℝ×ℝ=> ‖g t.1 t.2‖
  obtain ⟨c,hc⟩:= hi.bddAbove_image (f:=w) (show Continuous w from Continuous.norm hg).continuousOn
  have hw : ∀ᵐ t:ℝ,t∈Ι (-1:ℝ) 1→ ∀ x ∈ A,‖g x t‖ ≤ c := by
    apply ae_of_all; intro t ht x hx
    apply hc
    rw [uIoc_of_le (by norm_num : (-1:ℝ)≤1)] at ht
    exact ⟨(x,t),⟨hx,ht.1.le,ht.2⟩,rfl⟩
  have hh:=intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=volume) (F:=f) (F':=g) (x₀:=x) (a:=(-1:ℝ)) (b:=1) (s:=A) (bound:=fun _=>c)
    (Icc_mem_nhds (by linarith) (by linarith)) (Eventually.of_forall fun u=>(curC hf u).aestronglyMeasurable)
    ((curC hf x).intervalIntegrable ..) (curC hg x).aestronglyMeasurable
    hw intervalIntegrable_const (ae_of_all _ fun t ht x hx=>he x t)
  exact hh.2.const_mul (1/2)

def s (t:ℝ):=(1+t)/2
def T0 (a x t:ℝ):= a+s t*(x-a)
def W0 (a x t:ℝ):= cosh (T0 a x t)
def Wd (a x t:ℝ):= sinh (T0 a x t)
def denom (a:ℝ):= ment (W0 a)
variable (a:ℝ)(f₀:ℝ→ℝ)
def Rg (x t:ℝ):= W0 a x t*f₀ (T0 a x t)
def trav := fun x=>ment (Rg a f₀) x/denom a x
lemma trav_eq (x): trav a f₀ x=Pbar ((a+x)/2) ((x-a)/2) f₀:=by
  have he (t):T0 a x t=loc ((a+x)/2) ((x-a)/2) t:=by unfold T0 loc s;ring
  unfold trav denom Rg W0 Pbar normE normM de ment; simp_rw [he]

variable {f₀}
lemma dp (x):0<denom a x:= by
  have he : Continuous (W0 a x):=by unfold W0 T0 s;fun_prop
  have hi:= mean_mono continuous_const he (f:=fun _=>1) (fun x hx=>one_le_cosh _)
  rw [mean_const] at hi; apply lt_of_lt_of_le zero_lt_one hi

def G1 (x t:ℝ):=
  s t*(W0 a x t * deriv f₀ (T0 a x t)+Wd a x t*f₀ (T0 a x t))
def G2 (x t:ℝ):=
  s t^2 * (W0 a x t*ddf f₀ (T0 a x t)+
    2*Wd a x t*deriv f₀ (T0 a x t)+ W0 a x t*f₀ (T0 a x t))

variable {P:Cap}
lemma grTrav (h:Guard f₀ P):
    let R:=ment (Rg a f₀)
    let d:=ment (G1 a (f₀:=f₀))
    let e:=ment (G2 a (f₀:=f₀))
    (Continuous R ∧ Continuous d ∧ Continuous e) ∧
      (∀ x,HasDerivAt R (d x) x ∧ HasDerivAt d (e x) x ∧
        |R x|≤denom a x*P.a∧ |d x|≤denom a x*(P.b+P.a)∧
          |e x|≤denom a x*(P.c+2*P.b+P.a)):=by
  intro R d e
  have ht : contB (T0 a):=by unfold contB T0 s;apply (by fun_prop : Continuous fun x:ℝ×ℝ=> a+ ((1+x.2)/2)*(x.1-a))
  let g:=fun x:ℝ×ℝ=> T0 a x.1 x.2
  have hg:Continuous g:=ht
  have ha:Continuous (fun x:ℝ×ℝ=>cosh (g x)):= continuous_cosh.comp hg
  have hb:Continuous (fun x:ℝ×ℝ=>sinh (g x)):= continuous_sinh.comp hg
  have hc:Continuous (fun x:ℝ×ℝ=>f₀ (g x)):=h.h.continuous.comp hg
  have hd:Continuous (fun x:ℝ×ℝ=>deriv f₀ (g x)):=h.g.continuous.comp hg
  have hh:Continuous fun x:ℝ×ℝ=>s x.2:=by unfold s;fun_prop
  have h₁:contB (Rg a f₀):= ha.mul hc
  have h₂:contB (G1 a (f₀:=f₀)):= hh.mul ((ha.mul hd).add (hb.mul hc))
  have h₃:contB (G2 a (f₀:=f₀)):=(hh.pow 2).mul (((ha.mul (Continuous.comp h.c ht)).add
    ((continuous_const.mul hb).mul hd)).add (ha.mul hc))

  constructor
  · exact ⟨cmCont h₁,cmCont h₂,cmCont h₃⟩
  intro x
  have du(t u):HasDerivAt (fun x=>T0 a x t) (s t) u:=by
    convert (((((hasDerivAt_id' u).sub_const a).const_mul (s t))).const_add a) using 1 <;> first|rfl|ring
  have di(t u):HasDerivAt (fun z=>W0 a z t) (Wd a u t*s t) u:=
    (Real.hasDerivAt_cosh _).comp u (du t u)
  have dj(t u):HasDerivAt (fun z=>Wd a z t) (W0 a u t*s t) u:=
    (Real.hasDerivAt_sinh _).comp u (du t u)
  refine ⟨fmd h₁ h₂ ?_ x,fmd h₂ h₃ ?_ x,?_⟩
  · intro x t
    convert ((di t x).fun_mul ((h.Df (T0 a x t)).comp x (du t x))) using 1
    all_goals first|rfl|(unfold G1;dsimp;ring)
  · intro x t
    convert ((((di t x).fun_mul ((h.Db (T0 a x t)).comp x (du t x))).fun_add
      ((dj t x).fun_mul ((h.Df (T0 a x t)).comp x (du t x)))).const_mul (s t)) using 1
    all_goals first|rfl|(unfold G2;dsimp;ring)
  have H {K:ℝ} (f:ℝ→ℝ)(hc:Continuous f) (hf:∀ t∈Icc (-1:ℝ) 1,|f t| ≤ W0 a x t *K) :
      |mean0 f| ≤ denom a x*K:= by
    let F:=fun t=>K*W0 a x t
    have he : Continuous F:=continuous_const.mul (show Continuous (W0 a x) from
      continuous_cosh.comp (curC ht x))
    have h0 : mean0 F= K*denom a x:=mean_scale ..
    have h1: ∀ t∈Icc (-1:ℝ) 1,|f t|≤F t:=by
      intro t h; unfold F; rw [mul_comm]; exact hf t h
    apply abs_le.mpr
    have hi:= mean_mono he.neg hc (fun t ht=>(abs_le.mp (h1 t ht)).1)
    have hv:= mean_mono hc he (fun t ht=>(abs_le.mp (h1 t ht)).2)
    have he' : mean0 (-F)= -mean0 F:=by unfold mean0; simp
    rw [he'] at hi; constructor<;>linarith
  have hW(t):0≤ W0 a x t:=(cosh_pos _).le
  have hV(t): |Wd a x t|≤ W0 a x t:=by
    let l:=T0 a x t
    change |sinh l|≤cosh l
    nlinarith [Real.cosh_sq_sub_sinh_sq l, sq_abs (sinh l),cosh_pos l]
  have hi {g:ℝ→ℝ}(l:ℝ)(h:∀ t, |g t|≤l)(t):
      |W0 a x t * g (T0 a x t)|≤W0 a x t * l ∧
      |Wd a x t * g (T0 a x t)| ≤ W0 a x t * l := by
    rw [abs_mul,abs_mul,abs_of_nonneg (hW _)]
    exact ⟨mul_le_mul_of_nonneg_left (h _) (hW _),mul_le_mul (hV _) (h _) (abs_nonneg _) (hW _)⟩
  have hs(t)(hh:t∈Icc (-1:ℝ) 1):0 ≤ s t∧ s t≤1:=by unfold s;constructor<;>linarith [hh.1,hh.2]
  refine ⟨H _ (curC h₁ x) (fun t _=>(hi _ h.fa _).1), H _ (curC h₂ x) ?_, H _ (curC h₃ x) ?_⟩
  · intro t ht
    have hv:=hi _ h.fb t;have ha:=hi _ h.fa t
    unfold G1;rw [abs_mul,abs_of_nonneg (hs t ht).1]
    apply (mul_le_of_le_one_left (abs_nonneg _) (hs t ht).2).trans
    rw [mul_add]; exact Guard.absAdd hv.1 ha.2
  intro t ht
  have hv:=hi _ h.fc t;have hh:=hi _ h.fb t;have ha:=hi _ h.fa t
  unfold G2;rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
  apply (mul_le_of_le_one_left (_root_.abs_nonneg _) (pow_le_one₀ (hs t ht).1 (hs t ht).2)).trans
  rw [mul_add,mul_add,mul_assoc 2,show W0 a x t*(2*P.b)=2*(W0 a x t *P.b) from by ring]
  exact Guard.absAdd (Guard.absAdd hv.1 (Guard.absMul (by norm_num) hh.2)) ha.1
end GeneralMahler.SCal.Mid

end

end OAI
