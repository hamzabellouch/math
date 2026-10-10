import OAI.Analysis.LienardCycles.ScaledCoefficients

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
namespace QuinticLienard.QuinticProfile
open SmoothFlow SmoothFlow.AlgebraicExpr ArcFamilies ScaledProfile
noncomputable def xExpr : AlgebraicExpr (ℝ × ℝ) := sqrt (const 2*linear (ContinuousLinearMap.snd ℝ ℝ ℝ))
noncomputable def expr (a : Fin 6 → ℝ) : AlgebraicExpr (ℝ × ℝ) :=
  const (a 0)+const (a 1)*xExpr+const (a 2)*xExpr^2+const (a 3)*xExpr^3+
    const (a 4)*xExpr^4+const (a 5)*xExpr^5
noncomputable def profile (a : Fin 6 → ℝ) (q : ℝ × ℝ) : ℝ := poly a (root q.2)
lemma representation (a : Fin 6 → ℝ) : (expr a).eval=profile a := by
  funext q
  simp [expr,xExpr,profile,poly,root]
lemma regular (a : Fin 6 → ℝ) {q : ℝ × ℝ} (hq : 0<q.2) : (expr a).RegularAt q := by
  have hx : xExpr.RegularAt q := by
    simp [xExpr,RegularAt,eval]
    positivity
  have hp (n : ℕ) := regular_pow xExpr n hx
  simp only [expr,regular_add,regular_mul,regular_const,hx,hp,true_and]
lemma analytic (a : Fin 6 → ℝ) {q : ℝ × ℝ} (hq : 0<q.2) : ContDiffAt ℝ ω (profile a) q := by
  rw [←representation]
  exact (expr a).eval_analytic (regular a hq)
lemma local_flow (a : Fin 6 → ℝ) (x : State ℝ) (hx : 0<x.2.1) :
    ∃ f : State ℝ × ℝ → State ℝ, ContDiffAt ℝ ω f (x,0) ∧
      ∀ᶠ q in 𝓝 (x,(0:ℝ)), f (q.1,0)=q.1 ∧
        HasDerivAt (fun s => f (q.1,s)) (field (profile a) (f q)) q.2 := by
  simpa only [representation] using algebraic_profile_flow (expr a) x (regular a hx)
lemma profile_eq (a : Fin 6 → ℝ) (p h : ℝ) : profile a (p,h)=poly a (Real.sqrt (2*h)) := rfl
end QuinticLienard.QuinticProfile

end OAI
