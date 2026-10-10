import OAI.Analysis.LienardCycles.ClosedCutoff

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology ContDiff NNReal
namespace QuinticLienard.Sharpness
open SmoothFlow SmoothFlow.AlgebraicExpr GlobalODE PartialCalculus
abbrev Space := ℝ × (Plane × ℝ)
noncomputable def f (x : ℝ) : ℝ := 4*x-(20/3)*x^3+(8/5)*x^5
noncomputable def V (z : Space) : Space := (0,((z.2.1.2-z.1*f z.2.1.1,-z.2.1.1),-z.2.1.1*f z.2.1.1))
noncomputable def X : AlgebraicExpr Space := linear ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((ContinuousLinearMap.fst ℝ Plane ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (Plane × ℝ))))
noncomputable def Eps : AlgebraicExpr Space := linear (ContinuousLinearMap.fst ℝ ℝ (Plane × ℝ))
noncomputable def polynomial : AlgebraicExpr Space := const 4*X+const (-(20/3))*X^3+const (8/5)*X^5
lemma polynomial_eval (z : Space) : polynomial.eval z=f z.2.1.1 := by simp [polynomial,X,f];ring
lemma polynomial_regular (z : Space) : polynomial.RegularAt z := by simp [polynomial,X,regular_pow]
lemma field_contDiff : ContDiff ℝ ω V := by unfold V f;fun_prop
lemma local_flow (z : Space) :
    ∃ g : Space × ℝ → Space, ContDiffAt ℝ ω g (z,0) ∧
      ∀ᶠ q in 𝓝 (z,(0:ℝ)),g (q.1,0)=q.1 ∧ HasDerivAt (fun t=>g (q.1,t)) (V (g q)) q.2 := by
  let xp : Space →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((ContinuousLinearMap.fst ℝ Plane ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (Plane × ℝ)))
  let yp : Space →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp ((ContinuousLinearMap.fst ℝ Plane ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (Plane × ℝ)))
  let A : Space →L[ℝ] Space := (0 : Space →L[ℝ] ℝ).prod ((yp.prod (-xp)).prod 0)
  let I : ℝ →L[ℝ] Space := (0 : ℝ →L[ℝ] ℝ).prod (((ContinuousLinearMap.id ℝ ℝ).prod 0).prod 0)
  let J : ℝ →L[ℝ] Space := (0 : ℝ →L[ℝ] ℝ).prod ((0 : ℝ →L[ℝ] Plane).prod (ContinuousLinearMap.id ℝ ℝ))
  let W : Path Space → Path Space := fun u=>pathMap A u-pathMap I ((Eps*polynomial).onPaths u)-pathMap J ((X*polynomial).onPaths u)
  have hp := AlgebraicExpr.path_properties (Eps*polynomial) (show (Eps*polynomial).RegularAt z by simp [Eps,polynomial_regular])
  have hq := AlgebraicExpr.path_properties (X*polynomial) (show (X*polynomial).RegularAt z by simp [X,polynomial_regular])
  have hW : ContDiffAt ℝ ω W (constCLM z) :=
    ((pathMap A).contDiff.contDiffAt.sub ((pathMap I).contDiff.contDiffAt.comp _ hp.2.1)).sub
      ((pathMap J).contDiff.contDiffAt.comp _ hq.2.1)
  apply exists_analytic_local_flow_eventually W V z _ hW
  filter_upwards [hp.2.2,hq.2.2] with u hu hv t
  simp only [W,ContinuousMap.sub_apply,pathMap_apply,hu t,hv t,eval_mul,polynomial_eval]
  simp [A,I,J,xp,yp,Eps,X,V]
noncomputable def I2 (t : ℝ) : ℝ := t/2-Real.sin t*Real.cos t/2
noncomputable def I4 (t : ℝ) : ℝ := (3/4)*I2 t-(Real.sin t)^3*Real.cos t/4
noncomputable def I6 (t : ℝ) : ℝ := (5/6)*I4 t-(Real.sin t)^5*Real.cos t/6
lemma deriv_I2 (t : ℝ) : HasDerivAt I2 ((Real.sin t)^2) t := by
  have h := ((hasDerivAt_id t).div_const 2).sub (((Real.hasDerivAt_sin t).mul (Real.hasDerivAt_cos t)).div_const 2)
  convert! h using 1
  nlinarith [Real.sin_sq_add_cos_sq t]
lemma deriv_I4 (t : ℝ) : HasDerivAt I4 ((Real.sin t)^4) t := by
  have h := ((deriv_I2 t).const_mul (3/4)).sub ((((Real.hasDerivAt_sin t).pow 3).mul (Real.hasDerivAt_cos t)).div_const 4)
  convert! h using 1
  have hc : (Real.cos t)^2=1-(Real.sin t)^2 := by nlinarith [Real.sin_sq_add_cos_sq t]
  simp only [Pi.pow_apply]
  ring_nf
  rw [hc]
  ring
lemma deriv_I6 (t : ℝ) : HasDerivAt I6 ((Real.sin t)^6) t := by
  have h := ((deriv_I4 t).const_mul (5/6)).sub ((((Real.hasDerivAt_sin t).pow 5).mul (Real.hasDerivAt_cos t)).div_const 6)
  convert! h using 1
  have hc : (Real.cos t)^2=1-(Real.sin t)^2 := by nlinarith [Real.sin_sq_add_cos_sq t]
  simp only [Pi.pow_apply]
  ring_nf
  rw [hc]
  ring
noncomputable def q (s t : ℝ) : ℝ := -4*s^2*I2 t+(20/3)*s^4*I4 t-(8/5)*s^6*I6 t
lemma deriv_q (s t : ℝ) : HasDerivAt (q s) (-(s*Real.sin t)*f (s*Real.sin t)) t := by
  have h := (((deriv_I2 t).const_mul (-4*s^2)).add ((deriv_I4 t).const_mul ((20/3)*s^4))).sub ((deriv_I6 t).const_mul ((8/5)*s^6))
  convert! h using 1
  unfold f;ring
noncomputable def circle (s t : ℝ) : Space := (0,((s*Real.sin t,s*Real.cos t),q s t))
lemma circle_deriv (s t : ℝ) : HasDerivAt (circle s) (V (circle s t)) t := by
  have h := (hasDerivAt_const t (0:ℝ)).prodMk (((Real.hasDerivAt_sin t).const_mul s).prodMk ((Real.hasDerivAt_cos t).const_mul s) |>.prodMk (deriv_q s t))
  simpa [circle,V] using! h
@[simp] lemma circle_zero (s : ℝ) : circle s 0=(0,((0,s),0)) := by simp [circle,q,I2,I4,I6]
lemma q_turn (s : ℝ) : q s (2*Real.pi)=-Real.pi*s^2*(4-5*s^2+s^4) := by
  simp [q,I2,I4,I6,Real.sin_two_pi];ring
lemma circle_continuous (s : ℝ) : Continuous (circle s) := continuous_iff_continuousAt.mpr (fun t=>(circle_deriv s t).continuousAt)
end QuinticLienard.Sharpness

end OAI
