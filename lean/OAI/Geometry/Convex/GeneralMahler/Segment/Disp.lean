import OAI.Geometry.Convex.GeneralMahler.Segment.Small
import OAI.Geometry.Convex.GeneralMahler.Segment.Stats

namespace OAI
/-! §08 Short-width budgets. Endpoint deviations. -/
noncomputable section
open Set Filter Real MeasureTheory MeasureTheory.Measure
open scoped Topology Interval
namespace GeneralMahler.SCal.SE
open Tag Grid Jet Profile Segment
variable {f g:ℝ→ℝ}
lemma cLC (f:ℝ→ℝ)(hf:TestF f): Continuous (liftF f):=continuous_iff_continuousAt.mpr
  fun x=>(liftD hf x).continuousAt
lemma mean_cs (hf:Continuous f):
    mean0 f ^2 ≤ mean0 (fun x=> f x^2):=by
  let c:=mean0 f
  let g:=fun x=> f x^2 + ((-2*c)*f x+c^2)
  have hc:Continuous (fun x=>f x^2):=hf.pow _
  have hb:Continuous (fun x=>(-2*c)*f x):=continuous_const.mul hf
  have hi:= mean_mono continuous_const (show Continuous g from hc.add (hb.add continuous_const))
    (f:=fun _=>0) (fun x _=>by unfold g;nlinarith [sq_nonneg (f x-c)])
  unfold g at hi
  rw [mean_add hc (show Continuous (fun x=>-2*c*f x+c^2) from hb.add continuous_const),mean_add hb continuous_const,mean_scale,mean_const,mean_const] at hi
  unfold c at hi;linarith
lemma norm_cs (m h:ℝ) (hf:Continuous f):
    normE m h f^2 ≤ normE m h (fun x=>f x^2):=by
  let c:=normE m h f; let g:=fun x=> f x^2 + ((-2*c)*f x+c^2)
  have hc:Continuous (fun x=>f x^2):=hf.pow _
  have hb:Continuous (fun x=>(-2*c)*f x):=continuous_const.mul hf
  have hi:= neMono m h continuous_const (show Continuous g from hc.add (hb.add continuous_const))
    (f:=fun _=>0) (fun x _=>by unfold g;nlinarith [sq_nonneg (f x-c)])
  unfold g at hi
  rw [neAdd m h hc (show Continuous (fun x=> -2*c*f x+c^2) from hb.add continuous_const),neAdd m h hb continuous_const,neScale,neConst,neConst] at hi
  unfold c at hi;linarith
lemma vge (m h:ℝ)(hf:TestF f): 0 ≤ vdis f (seg m h):=by
  unfold vdis sqav
  rw [sub_nonneg,bav_norm m h _ hf.cont,bav_norm m h _ (sq_test hf).cont]
  exact norm_cs m h ((cLC f hf).comp (cLoc ..))
-- Helpers optional zero test pair f+g²
lemma bav_ex (m h:ℝ)(hf:TestF f):
    bav f (seg m h)=normE m h (fun x=>liftF f (loc m h x)):=bav_norm m h f hf.cont
def errorF (m h:ℝ)(f:ℝ→ℝ)(s:ℝ)(x:ℝ):=(liftF f (loc m h x)-liftF f (loc m h s))^2
lemma cEF (m h:ℝ)(hf:TestF f)(s:ℝ):Continuous (errorF m h f s):=
  (((cLC _ hf).comp (cLoc ..)).sub continuous_const).pow _
lemma b_repr (m h:ℝ)(f:ℝ→ℝ)(hf:TestF f):
    mdis f (seg m h)=normE m h (errorF m h f 1)∧
      mdis f (seg m h).swap=normE m h (errorF m h f (-1)):=by
  let t (c:ℝ):=fun x=>(f x-c)^2
  have ht (c:ℝ): TestF (t c):=sq_test (hf.sub (TestF.const _))
  let v:=seg m h
  have he₁:loc m h 1=right m h:=by unfold loc right; ring
  have he₂:loc m h (-1)=left m h:=by unfold loc left;ring
  constructor
  · rw [mdis_eq hf v,bav_ex m h (ht (f v.2))]
    unfold t errorF liftF;rw [he₁]; rfl
  rw [mdis_eq hf v.swap,bav_sym (ht (f v.swap.2)) v,bav_ex m h (ht (f v.swap.2))]
  unfold t errorF liftF;rw [he₂];rfl

lemma efbound {L:ℝ} (hf:TestF f) (hg:TestF g)
    (hfg:∀ x y:ℝ,(liftF f x-liftF f y)^2+(liftF g x-liftF g y)^2≤L*(x-y)^2)
    (m h:ℝ)(hh:0<h)(he:h≤3/10)(hl:0≤L):
    let v:=seg m h
    let a:=(mdis f v+mdis g v+mdis f v.swap+mdis g v.swap)/2
    0≤ a ∧ a ≤ L*h^2*(4/3+(5/100)*h^2):=by
  intro v a
  let G := fun (t x:ℝ)=> errorF m h f t x+errorF m h g t x
  let F := fun x=> (1/2:ℝ)*(G 1 x+G (-1) x)
  have hp (t): Continuous (G t):= (cEF m h hf _).add (cEF m h hg _)
  have hv:Continuous F:=continuous_const.mul ((hp _).add (hp _))
  have heq:a=normE m h F:=by
    have hyp (t):normE m h (G t)=normE m h (errorF m h f t)+normE m h (errorF m h g t):=
      neAdd m h (cEF m h hf _) (cEF m h hg _)
    obtain ⟨h1,h2⟩:=b_repr m h f hf; obtain ⟨h3,h4⟩:=b_repr m h g hg
    unfold F a v
    rw [h1,h2,h3,h4,neScale,neAdd m h (hp _) (hp _),hyp,hyp]; ring
  rw [heq]; constructor
  · have hj:=neMono m h continuous_const hv (f:=fun _=>0) (fun x _=> by unfold F G errorF; positivity)
    rwa [neConst] at hj
  let l:= fun x:ℝ=> L*h^2*(1+x^2)
  have hu:=neMono m h hv (show Continuous l by unfold l;fun_prop) ?_
  · apply hu.trans
    unfold l
    rw [neScale,neAdd m h continuous_const (show Continuous (fun x:ℝ=>x^2) by fun_prop),
      neConst]
    have hd:=mβ m hh he
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  intro x hx
  have hf(t):G t x ≤ L*(loc m h x-loc m h t)^2:=hfg _ _
  unfold l F
  have h1:=hf 1;have h2:= hf (-1); unfold loc at h1 h2;linarith

lemma cirLip (x y:ℝ):
    (lc x-lc y)^2+(ls x-ls y)^2≤wp*(x-y)^2:=by
  let a:= omegaP*x; let b:=omegaP*y
  have he:=sin_sq_le_sq (x:=(a-b)/2)
  have h1:= sin_sq_add_cos_sq a;have h2:=sin_sq_add_cos_sq b
  have hh:= Real.sin_sq_eq_half_sub ((a-b)/2)
  rw [show 2*((a-b)/2)=a-b by ring,cos_sub] at hh
  rw [lc_e,lc_e,ls_e,ls_e]; unfold wp
  have h:(cos a-cos b)^2+(sin a-sin b)^2≤ (omegaP*(x-y))^2:=by
    rw [show omegaP*(x-y)=a-b from by unfold a b;ring]; linarith
  unfold a b at h; nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg r)]

lemma pa_short (m:ℝ){h:ℝ}(hh:0<h)(he:h≤3/10):
    0 ≤ pa (seg m h)∧ pa (seg m h) ≤ wp*h^2*(4/3+(5/100)*h^2):=by
  have hi:= efbound ucs_reg.1 ucs_reg.2 cirLip m h hh he wp_pos.le
  unfold pa pPlus; simpa only [add_assoc] using hi
lemma qLip (H:NG)(x y:ℝ): (qu (xs x)-qu (xs y))^2 ≤(193/1000:ℝ)^2*(x-y)^2:=by
  have h1 {x y:ℝ}(h:x≤y): |qu (xs y)-qu (xs x)| ≤(193/1000)*(y-x) :=
    dist_bdd (hqt H) _ h fun z _=>by
      apply abs_le.mpr
      have hi:= SE.hdQ H z; norm_num at *; exact hi
  rcases le_total x y with hx|hx
  · have hi:=h1 hx
    nlinarith [sq_le_sq.mpr (hi.trans (le_abs_self _))]
  have hi:= h1 hx
  nlinarith [sq_le_sq.mpr (hi.trans (le_abs_self _))]
lemma ba_short (H:NG)(m:ℝ){h:ℝ}(hh:0<h)(he:h≤3/10):
    0 ≤ ba (seg m h)∧ ba (seg m h) ≤ (193/1000:ℝ)^2*h^2*(4/3+(5/100)*h^2):=by
  let v:=seg m h
  have hu(x y:ℝ):
      (liftF qu x-liftF qu y)^2+(liftF (fun _=>0) x-liftF (fun _=>0) y)^2≤
        (193/1000:ℝ)^2*(x-y)^2:=by simpa only [liftF,sub_self,pow_two,zero_mul,add_zero] using qLip H x y
  have hi:= efbound (hqt H) (TestF.const 0) hu m h hh he (by positivity)
  have hj (v:Plane): mdis (fun _=>0) v=0:= by simp [mdis,sqav,bav]
  unfold ba qPlus; simpa only [hj,add_zero] using hi
end GeneralMahler.SCal.SE

end

end OAI
