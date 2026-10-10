import OAI.Analysis.LienardCycles.PositiveFit

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ScaledProfile
open SmoothFlow.AlgebraicExpr PartialCalculus ArcFamilies
noncomputable def root (h : ℝ) : ℝ := Real.sqrt (2*h)
noncomputable def slope (a : Fin 6 → ℝ) (h : ℝ) : ℝ := c₁ a (root h)/root h
noncomputable def curvature (a : Fin 6 → ℝ) (h : ℝ) : ℝ :=
  2*c₂ a (root h)/(root h)^2-c₁ a (root h)/(root h)^3
noncomputable def third (a : Fin 6 → ℝ) (h : ℝ) : ℝ := 6*rem a (root h) (root h) 0
lemma third_formula (a : Fin 6 → ℝ) {h : ℝ} (hh : 0<h) :
    third a h=3*(a 1-a 3*(root h)^2+5*a 5*(root h)^4)/(root h)^5 := by
  have hx : 0<root h := Real.sqrt_pos.mpr (by positivity)
  dsimp [third,rem,c₁,c₂,c₃,c₄]
  field_simp
  ring
lemma epsilon_zero (a : Fin 6 → ℝ) (c u r t : ℝ) :
    Φ a c (((u,r),0),t)=r*slope a (c+u^2+r^2)*(t-1)+
      r^3*curvature a (c+u^2+r^2)*(t-1)^2/2 := by
  simp [Φ,Expr,K,B,X,slope,curvature,root]
lemma rho_zero_epsilon (a : Fin 6 → ℝ) (c u e t : ℝ) :
    Φ a c (((u,0),e),t)=e*third a (c+u^2)*(t-1)^3/6 := by
  simp only [Φ,Expr,eval_add,eval_mul,eval_sub,eval_div,eval_pow,eval_const,eval_ρ,
    eval_ε,eval_s,zero_mul,zero_pow (by norm_num : (3:ℕ)≠0),zero_div,add_zero,zero_add]
  simp only [η,eval_mul,eval_pow,eval_sub,eval_s,eval_const,eval_Rem]
  simp [X,Z,Δ,root,third]
  ring
lemma epsilon_cubic {a : Fin 6 → ℝ} {c : ℝ} (hc : 0<c) (u : ℝ) {t : ℝ} (ht : 0<t) :
    first (fun q : ℝ × ℝ => Φ a c (((u,0),q.1),q.2)) (0,t)=third a (c+u^2)*(t-1)^3/6 := by
  have ha : ContDiffAt ℝ ω (fun q : ℝ × ℝ => Φ a c (((u,0),q.1),q.2)) (0,t) :=
    (analytic hc ht).comp (0,t) ((contDiffAt_const.prodMk contDiffAt_fst).prodMk contDiffAt_snd)
  apply (first_hasDerivAt (ha.differentiableAt (by simp))).unique
  have hd := (((hasDerivAt_id (0:ℝ)).mul_const (third a (c+u^2))).mul_const ((t-1)^3)).div_const 6
  simpa only [rho_zero_epsilon,one_mul,id_eq] using! hd
noncomputable def fitSlope (a : Fin 6 → ℝ) (c : ℝ) : Params → ℝ := PositiveFit.d (Φ a c) 1 1
noncomputable def fitCurvature (a : Fin 6 → ℝ) (c : ℝ) : Params → ℝ := PositiveFit.k (Φ a c) 1 1
lemma fitSlope_analytic {a : Fin 6 → ℝ} {c : ℝ} (hc : 0<c) (p : Params) :
    ContDiffAt ℝ ω (fitSlope a c) p :=
  PositiveFit.d_analytic (Φ a c) (fun _ h => analytic hc h) (local_flow a hc) (by norm_num) (by norm_num)
lemma fitCurvature_analytic {a : Fin 6 → ℝ} {c : ℝ} (hc : 0<c) (p : Params) :
    ContDiffAt ℝ ω (fitCurvature a c) p :=
  PositiveFit.k_analytic (Φ a c) (fun _ h => analytic hc h) (local_flow a hc) (by norm_num) (by norm_num)
lemma fit_epsilon_zero {a : Fin 6 → ℝ} {c : ℝ} (hc : 0<c) (u r : ℝ) :
    fitSlope a c ((u,r),0)=r*slope a (c+u^2+r^2) ∧
    fitCurvature a c ((u,r),0)=r^3*curvature a (c+u^2+r^2) := by
  apply PositiveFit.fit_quadratic (Φ a c) (fun _ h => analytic hc h) (local_flow a hc)
    (by norm_num) (by norm_num)
  intro x
  rw [epsilon_zero,epsilon_zero]
  ring
lemma fit_cubic {a : Fin 6 → ℝ} {c : ℝ} (hc : 0<c) (u : ℝ) :
    HasDerivAt (fun e => fitSlope a c ((u,0),e)) (-third a (c+u^2)/35) 0 ∧
    HasDerivAt (fun e => fitCurvature a c ((u,0),e)) (2*third a (c+u^2)/7) 0 := by
  apply PositiveFit.cubic_fit (Φ a c) (fun _ h => analytic hc h) (local_flow a hc)
    (contDiff_const.prodMk contDiff_id) (base_zero a c) (rho_zero a c u) (by norm_num)
  intro x hx
  exact epsilon_cubic hc u hx
end QuinticLienard.ScaledProfile

end OAI
