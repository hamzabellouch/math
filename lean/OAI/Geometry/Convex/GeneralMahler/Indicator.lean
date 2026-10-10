import OAI.Geometry.Convex.GeneralMahler.Kernel

namespace OAI
/-! p-to-indicator score and layer integration formulas. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers Profile
def jump (z y:ℝ) := if y≤z then (1:ℝ) else 0
lemma jump_m : Measurable (Function.uncurry jump) :=
  Measurable.ite ((isClosed_le continuous_snd continuous_fst).measurableSet)
    measurable_const measurable_const
def score (z y:ℝ) := p z-jump z y

lemma score_m : Measurable score.uncurry := (cp.measurable.comp measurable_fst).sub jump_m

lemma score_rapid : mixed score := by
  let f := fun z (_:ℝ)=> p z-st z
  let g := fun z y=>st z-jump z y
  rw [show score=fun z y=> f z y+g z y from funext fun x=>funext fun y=>by unfold score f g; ring]
  apply (mixed.of_rapid rapid_p).add
  apply mixed.of_cutoff (show PolyBound g.uncurry from PolyBound.of_bound 1 fun ⟨x,y⟩=>by
    change ‖st x-jump x y‖≤1; unfold st jump; split_ifs <;> norm_num)
    (show PolyBound (fun x:ℝ=>‖x‖) from PolyBound.id.norm)
  intro x y hx
  simp only [Real.norm_eq_abs] at hx
  unfold g st jump; split_ifs <;> grind

def ss (f:ℝ→ℝ) (z y:ℝ) := score z y * deriv f z
lemma ss_m {f:ℝ→ℝ} (hf:TestF f) : mixed (ss f) :=
  score_rapid.product (g:=fun x _=>deriv f x) (show PolyBound (fun u:Plane=> deriv f u.1) from hf.der.poly.comp PolyBound.fst)
    fun _x _y=> (norm_mul _ _).le
lemma ss_sm (f) : Measurable (ss f).uncurry :=
  score_m.mul ((measurable_deriv f).comp measurable_fst)

lemma centered_s {f:ℝ→ℝ} (hf:TestF f) (x:ℝ) :
    (∫ z,ss f z x)= f x-ga f := by
  let g := fun z=>ss f z x+phi z*f z
  have hg (t:ℝ) : HasDerivAt (fun z=>p z*f z)
      (phi t*f t+p t*deriv f t) t :=
    (d_p t).fun_mul (hf.diff t).hasDerivAt
  have hg' (t:ℝ) : HasDerivAt (fun z=>(p z-1)*f z)
      (phi t*f t+(p t-1)*deriv f t) t :=
    ((d_p t).sub_const 1).fun_mul (hf.diff t).hasDerivAt
  have ht := rapid_p.product hf.poly
  have hi := mixed_integrable_left (μ:=volume) (ss_m hf) x
    ((ss_sm f).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hh : Integrable g := hi.add (ga_i hf)
  have h₀ : Tendsto (fun x=>p x*f x) atBot (𝓝 0) := by
    apply Tendsto.congr' _ ht.tail_limit_bot
    filter_upwards [eventually_lt_atBot (0:ℝ)] with z hz; simp [st,not_le_of_gt hz]
  have h₁ : Tendsto (fun x=>(p x-1)*f x) atTop (𝓝 0) := by
    apply Tendsto.congr' _ ht.tail_limit
    filter_upwards [eventually_ge_atTop (0:ℝ)] with z hz; simp [st,hz]
  have ha : (∫ t in Iic x,g t)=p x*f x := by
    have hh := integral_Iic_of_hasDerivAt_of_tendsto ((hg x).continuousAt.continuousWithinAt)
      (fun t ht => ?_) hh.integrableOn h₀
    · simpa using hh
    have he : g t=phi t*f t+p t*deriv f t := by simp only [g,ss,score,jump,
      ite_eq_right (not_le_of_gt (mem_Iio.mp ht)),sub_zero]; ring
    exact he.symm ▸ hg t
  have hb : (∫ t in Ioi x,g t)= -((p x-1)*f x) := by
    have hh := integral_Ioi_of_hasDerivAt_of_tendsto ((hg' x).continuousAt.continuousWithinAt)
      (fun t ht => ?_) hh.integrableOn h₁
    · simpa using hh
    have he : g t=phi t*f t+(p t-1)*deriv f t :=
      by simp only [g,ss,score,jump,ite_eq_left (mem_Ioi.mp ht).le]; ring
    exact he.symm ▸ hg' t
  have hx : (∫ t,g t)=f x := by
    rw [← integral_add_compl measurableSet_Iic (s:=Iic x) hh,compl_Iic,ha,hb]; ring
  rw [show (∫ t,g t) = _ from integral_add hi (ga_i hf)] at hx
  unfold ga; linarith

lemma two_scores {f j:ℝ→ℝ} (hf:TestF f) (hj:TestF j) :
    mixed fun u:Plane => fun y=>ss f u.1 y*ss j u.2 y := by
  intro n
  obtain ⟨C,m,hc,h⟩ := ss_m hf n
  obtain ⟨D,k,hd,h'⟩ := ss_m hj n
  use C*D,m+k,mul_nonneg hc hd
  intro u y
  rw [norm_mul]
  have ha : (1+‖u‖)^n ≤ (1+‖u.1‖)^n*(1+‖u.2‖)^n := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    change 1+max _ _ ≤ _
    rcases max_choice ‖u.1‖ ‖u.2‖ with h|h <;> rw [h] <;> nlinarith [norm_nonneg u.1,norm_nonneg u.2]
  apply le_trans (mul_le_mul_of_nonneg_left ha (by positivity))
  calc
    _ = (‖ss f u.1 y‖*(1+‖u.1‖)^n)*(‖ss j u.2 y‖*(1+‖u.2‖)^n) := by ring
    _ ≤ _ := mul_le_mul (h _ _) (h' _ _) (by positivity) (by positivity)
    _ = _ := by rw [pow_add]; ring

lemma moment_mix {w:ℝ→ℝ} (hw:MomentF w) (hm:Measurable w) (hp:∀ x,0≤w x)
    {f:Plane→ℝ→ℝ} (hf:mixed f) (hf':Measurable f.uncurry) :
    Integrable (fun v:Plane×ℝ=> w v.2*f v.1 v.2) := by
  let d := Module.finrank ℝ Plane+1
  obtain ⟨C,n,hc,h⟩ := hf d
  let b := fun x:Plane=> ((1+‖x‖)^d)⁻¹
  have hh : Integrable b := envelope_inv_int
  let g := fun x:ℝ=>w x * (C*(1+‖x‖)^n)
  have hg : Integrable g := hw _ (by fun_prop)
    ((PolyBound.const _).mul (((PolyBound.const _).add PolyBound.id.norm).pow n))
  apply (hh.mul_prod hg).mono' ((hm.comp measurable_snd).mul hf').aestronglyMeasurable
    (ae_of_all _ ?_)
  rintro ⟨x,y⟩
  change ‖w y*f x y‖ ≤ b x*g y
  rw [norm_mul,Real.norm_of_nonneg (hp _)]
  have he : ‖f x y‖ ≤ C*(1+‖y‖)^n*b x := by
    unfold b
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact h x y
  unfold g
  apply le_trans (mul_le_mul_of_nonneg_left he (hp _)); apply le_of_eq; ring

variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m)
def Hcov (u:Plane) := q.s0*p u.1*p u.2 - p u.1*q.avH u.2 - q.avH u.1*p u.2+
  q.avH (min u.1 u.2)
lemma H_jump (x:ℝ) :
    (∫ z,q.layerW z*jump x z)=q.avH x := by
  rw [show (fun z=>q.layerW z*jump x z)=(Iic x).indicator q.layerW from by ext t; by_cases h:t≤x <;> simp [jump,h]]
  rw [integral_indicator measurableSet_Iic]
  have hh := integral_Iic_of_hasDerivAt_of_tendsto'
    (f:=q.avH) (a:=x) (fun t _=>q.H_deriv t) q.integrable_w.integrableOn q.H_bot
  simpa using hh

lemma H_score (u:Plane) : q.Hcov u=∫ y,q.layerW y*(score u.1 y*score u.2 y) := by
  let f := fun x z => q.layerW z*jump x z
  have hi (x) : Integrable (f x) := q.moment_w (jump x)
    (jump_m.comp (measurable_const.prodMk measurable_id)) (PolyBound.of_bound 1
      (fun y=>by unfold jump; split<;>norm_num))
  set a := u.1; set b := u.2
  have he (y) : q.layerW y*(score a y*score b y) =
      (q.layerW y*(p a*p b)-f b y*p a-f a y*p b)+f (min a b) y := by
    unfold f score
    have hh : jump a y*jump b y=jump (min a b) y := by unfold jump; split_ifs <;> grind
    rw [← hh]; ring
  simp_rw [he]
  have ha := (hi a).mul_const (p b)
  have hb := (hi b).mul_const (p a)
  have hd := q.integrable_w.mul_const (p a*p b)
  rw [integral_add,integral_sub,integral_sub hd hb]
  · unfold f; simp_rw [integral_mul_const, q.H_jump,q.integral_w]
    unfold Hcov a b; ring
  all_goals first | exact hi _ | exact ha | exact hd.sub hb | exact (hd.sub hb).sub ha

lemma H_cov_I {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) :
    Integrable (fun x:Plane=>q.Hcov x*(deriv f x.1*deriv g x.2)) ∧
    (∫ x:Plane,q.Hcov x*(deriv f x.1*deriv g x.2))=
      ∫ x,q.layerW x*((f x-ga f)*(g x-ga g)) := by
  let F := fun u:Plane=>fun x:ℝ=>ss f u.1 x*ss g u.2 x
  let C := fun u:Plane×ℝ=>q.layerW u.2*F u.1 u.2
  have hm : Measurable F.uncurry :=
    ((ss_sm f).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      ((ss_sm g).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hi : Integrable C :=
    moment_mix q.moment_w q.w_cont.measurable (fun x=>(q.w_positive x).le) (two_scores hf hg) hm
  have hh (u:Plane) : q.Hcov u*(deriv f u.1*deriv g u.2)=∫ y,C (u,y) := by
    rw [q.H_score, ← integral_mul_const]
    congr 1; ext; unfold C F ss; ring
  simp_rw [hh]
  refine ⟨hi.integral_prod_left,?_⟩
  rw [integral_integral_swap]
  · congr 1; ext y; dsimp only [C,F]; rw [integral_const_mul,show (volume:Measure Plane)=volume.prod volume from rfl,
      integral_prod_mul (fun x=>ss f x y) (fun x=>ss g x y), centered_s hf,centered_s hg]
  exact hi
end ProjField
end GeneralMahler

end

end OAI
