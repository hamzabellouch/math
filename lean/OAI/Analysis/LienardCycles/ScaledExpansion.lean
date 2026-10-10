import OAI.Analysis.LienardCycles.ScaledAlgebraic

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ScaledProfile
open SmoothFlow.AlgebraicExpr
noncomputable def poly (a : Fin 6 → ℝ) (x : ℝ) : ℝ :=
  a 0+a 1*x+a 2*x^2+a 3*x^3+a 4*x^4+a 5*x^5
noncomputable def c₁ (a : Fin 6 → ℝ) (x : ℝ) : ℝ := a 1+2*a 2*x+3*a 3*x^2+4*a 4*x^3+5*a 5*x^4
noncomputable def c₂ (a : Fin 6 → ℝ) (x : ℝ) : ℝ := a 2+3*a 3*x+6*a 4*x^2+10*a 5*x^3
noncomputable def c₃ (a : Fin 6 → ℝ) (x : ℝ) : ℝ := a 3+4*a 4*x+10*a 5*x^2
noncomputable def c₄ (a : Fin 6 → ℝ) (x : ℝ) : ℝ := a 4+5*a 5*x
noncomputable def rem (a : Fin 6 → ℝ) (x z δ : ℝ) : ℝ :=
  -2*(c₂ a x-c₁ a x/(2*x))*(z+3*x)/(x^2*(z+x)^3)+8*c₃ a x/(z+x)^3+
    16*c₄ a x*δ/(z+x)^4+32*a 5*δ^2/(z+x)^5
@[simp] lemma eval_C₁ (a : Fin 6 → ℝ) (x : SmoothFlow.AlgebraicExpr Dom) (q : Dom) :
    (C₁ a x).eval q=c₁ a (x.eval q) := by simp [C₁,c₁]
@[simp] lemma eval_C₂ (a : Fin 6 → ℝ) (x : SmoothFlow.AlgebraicExpr Dom) (q : Dom) :
    (C₂ a x).eval q=c₂ a (x.eval q) := by simp [C₂,c₂]
@[simp] lemma eval_C₃ (a : Fin 6 → ℝ) (x : SmoothFlow.AlgebraicExpr Dom) (q : Dom) :
    (C₃ a x).eval q=c₃ a (x.eval q) := by simp [C₃,c₃]
@[simp] lemma eval_C₄ (a : Fin 6 → ℝ) (x : SmoothFlow.AlgebraicExpr Dom) (q : Dom) :
    (C₄ a x).eval q=c₄ a (x.eval q) := by simp [C₄,c₄]
@[simp] lemma eval_Rem (a : Fin 6 → ℝ) (c : ℝ) (q : Dom) :
    (Rem a c).eval q=rem a ((X c).eval q) ((Z c).eval q) (Δ.eval q) := by simp [Rem,rem]
lemma polynomial_taylor (a : Fin 6 → ℝ) (x z : ℝ) :
    poly a z-poly a x=c₁ a x*(z-x)+c₂ a x*(z-x)^2+c₃ a x*(z-x)^3+c₄ a x*(z-x)^4+a 5*(z-x)^5 := by
  dsimp [poly,c₁,c₂,c₃,c₄]
  ring
lemma rational_taylor (b₁ b₂ b₃ b₄ b₅ : ℝ) {x z δ : ℝ} (hx : x≠0) (hxz : z+x≠0)
    (hδ : δ=(z-x)*(z+x)/2) :
    b₁*(z-x)+b₂*(z-x)^2+b₃*(z-x)^3+b₄*(z-x)^4+b₅*(z-x)^5 =
      b₁/x*δ+(2*b₂/x^2-b₁/x^3)*δ^2/2+
      δ^3*(-2*(b₂-b₁/(2*x))*(z+3*x)/(x^2*(z+x)^3)+8*b₃/(z+x)^3+
        16*b₄*δ/(z+x)^4+32*b₅*δ^2/(z+x)^5) := by
  rw [hδ]
  field_simp
  ring
lemma expansion (a : Fin 6 → ℝ) {x z δ : ℝ} (hx : x≠0) (hxz : z+x≠0)
    (hδ : δ=(z-x)*(z+x)/2) :
    poly a z-poly a x=c₁ a x/x*δ+(2*c₂ a x/x^2-c₁ a x/x^3)*δ^2/2+δ^3*rem a x z δ := by
  rw [polynomial_taylor]
  exact rational_taylor _ _ _ _ _ hx hxz hδ
lemma actual_scaling (a : Fin 6 → ℝ) {c u r t : ℝ} (hc : 0<c) (hr : 0<r) (ht : 0<t) :
    poly a (Real.sqrt (2*(c+u^2+r^2*t)))-poly a (Real.sqrt (2*(c+u^2+r^2))) =
      r*Φ a c (((u,r),r^5),t) := by
  let q : Dom := (((u,r),r^5),t)
  let x := (X c).eval q
  let z := (Z c).eval q
  let δ := Δ.eval q
  have hx : 0<x := X_pos hc q
  have hz : 0<z := Z_pos hc ht
  have hxx : x^2=2*(c+u^2+r^2) := by
    dsimp [x,q]
    simp only [X,eval_sqrt,eval_mul,eval_const,eval_add,eval_pow,eval_A,eval_ρ]
    exact Real.sq_sqrt (by positivity)
  have hzz : z^2=2*(c+u^2+r^2*t) := by
    dsimp [z,q]
    simp only [Z,eval_sqrt,eval_mul,eval_const,eval_add,eval_pow,eval_A,eval_ρ,eval_s]
    exact Real.sq_sqrt (by positivity)
  have hδ : δ=(z-x)*(z+x)/2 := by
    have he : δ=r^2*(t-1) := by simp [δ,Δ,q]
    rw [he]
    nlinarith only [hxx,hzz]
  have hE := expansion a hx.ne' (add_pos hz hx).ne' hδ
  have hex : x=Real.sqrt (2*(c+u^2+r^2)) := by simp [x,X,q]
  have hez : z=Real.sqrt (2*(c+u^2+r^2*t)) := by simp [z,Z,q]
  rw [←hex,←hez,hE]
  change _=r*(Expr a c).eval q
  simp only [Expr,K,B,η,eval_add,eval_mul,eval_sub,eval_div,eval_pow,eval_const,
    eval_ρ,eval_s,eval_ε,eval_C₁,eval_C₂,eval_Rem]
  change _=r*(r*(c₁ a x/x)*(t-1)+r^3*(2*c₂ a x/x^2-c₁ a x/x^3)*(t-1)^2/2+
    r^5*((t-1)^3*rem a x z δ))
  have he : δ=r^2*(t-1) := by simp [δ,Δ,q]
  rw [he]
  ring
end QuinticLienard.ScaledProfile

end OAI
