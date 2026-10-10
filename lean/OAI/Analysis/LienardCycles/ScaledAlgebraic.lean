import OAI.Analysis.LienardCycles.AlgebraicNotation

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
open SmoothFlow SmoothFlow.AlgebraicExpr ArcFamilies
abbrev Params := (ℝ × ℝ) × ℝ
abbrev Dom := Params × ℝ
noncomputable def A : AlgebraicExpr Dom := linear
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    ((ContinuousLinearMap.fst ℝ (ℝ×ℝ) ℝ).comp (ContinuousLinearMap.fst ℝ Params ℝ)))
noncomputable def ρ : AlgebraicExpr Dom := linear
  ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    ((ContinuousLinearMap.fst ℝ (ℝ×ℝ) ℝ).comp (ContinuousLinearMap.fst ℝ Params ℝ)))
noncomputable def ε : AlgebraicExpr Dom := linear
  ((ContinuousLinearMap.snd ℝ (ℝ×ℝ) ℝ).comp (ContinuousLinearMap.fst ℝ Params ℝ))
noncomputable def s : AlgebraicExpr Dom := linear (ContinuousLinearMap.snd ℝ Params ℝ)
noncomputable def X (c : ℝ) : AlgebraicExpr Dom := sqrt ((const 2)*(const c+A^2+ρ^2))
noncomputable def Z (c : ℝ) : AlgebraicExpr Dom := sqrt ((const 2)*(const c+A^2+ρ^2*s))
noncomputable def Δ : AlgebraicExpr Dom := ρ^2*(s-const 1)
noncomputable def C₁ (a : Fin 6 → ℝ) (x : AlgebraicExpr Dom) : AlgebraicExpr Dom :=
  const (a 1)+(const 2)*const (a 2)*x+(const 3)*const (a 3)*x^2+(const 4)*const (a 4)*x^3+(const 5)*const (a 5)*x^4
noncomputable def C₂ (a : Fin 6 → ℝ) (x : AlgebraicExpr Dom) : AlgebraicExpr Dom :=
  const (a 2)+(const 3)*const (a 3)*x+(const 6)*const (a 4)*x^2+(const 10)*const (a 5)*x^3
noncomputable def C₃ (a : Fin 6 → ℝ) (x : AlgebraicExpr Dom) : AlgebraicExpr Dom :=
  const (a 3)+(const 4)*const (a 4)*x+(const 10)*const (a 5)*x^2
noncomputable def C₄ (a : Fin 6 → ℝ) (x : AlgebraicExpr Dom) : AlgebraicExpr Dom :=
  const (a 4)+(const 5)*const (a 5)*x
noncomputable def K (a : Fin 6 → ℝ) (c : ℝ) : AlgebraicExpr Dom := C₁ a (X c)/X c
noncomputable def B (a : Fin 6 → ℝ) (c : ℝ) : AlgebraicExpr Dom :=
  (const 2)*C₂ a (X c)/(X c)^2-C₁ a (X c)/(X c)^3
noncomputable def Rem (a : Fin 6 → ℝ) (c : ℝ) : AlgebraicExpr Dom :=
  -(const 2)*(C₂ a (X c)-C₁ a (X c)/((const 2)*X c))*(Z c+(const 3)*X c)/((X c)^2*(Z c+X c)^3)+
    (const 8)*C₃ a (X c)/(Z c+X c)^3+(const 16)*C₄ a (X c)*Δ/(Z c+X c)^4+
    (const 32)*const (a 5)*Δ^2/(Z c+X c)^5
noncomputable def η (a : Fin 6 → ℝ) (c : ℝ) : AlgebraicExpr Dom := (s-const 1)^3*Rem a c
noncomputable def Expr (a : Fin 6 → ℝ) (c : ℝ) : AlgebraicExpr Dom :=
  ρ*K a c*(s-const 1)+ρ^3*B a c*(s-const 1)^2/(const 2)+ε*η a c
noncomputable def Φ (a : Fin 6 → ℝ) (c : ℝ) : Dom → ℝ := (Expr a c).eval

@[simp] lemma eval_A (q : Dom) : A.eval q=q.1.1.1 := rfl
@[simp] lemma eval_ρ (q : Dom) : ρ.eval q=q.1.1.2 := rfl
@[simp] lemma eval_ε (q : Dom) : ε.eval q=q.1.2 := rfl
@[simp] lemma eval_s (q : Dom) : s.eval q=q.2 := rfl
@[simp] lemma regular_A (q : Dom) : A.RegularAt q := trivial
@[simp] lemma regular_ρ (q : Dom) : ρ.RegularAt q := trivial
@[simp] lemma regular_ε (q : Dom) : ε.RegularAt q := trivial
@[simp] lemma regular_s (q : Dom) : s.RegularAt q := trivial
lemma X_pos {c : ℝ} (hc : 0<c) (q : Dom) : 0<(X c).eval q := by
  simp only [X,eval_sqrt,eval_mul,eval_add,eval_const,eval_pow,eval_A,eval_ρ]
  apply Real.sqrt_pos.mpr
  positivity
lemma Z_pos {c : ℝ} (hc : 0<c) {q : Dom} (hq : 0<q.2) : 0<(Z c).eval q := by
  simp only [Z,eval_sqrt,eval_mul,eval_add,eval_const,eval_pow,eval_A,eval_ρ,eval_s]
  apply Real.sqrt_pos.mpr
  positivity
lemma X_regular {c : ℝ} (hc : 0<c) (q : Dom) : (X c).RegularAt q := by
  simp only [X,regular_sqrt,regular_mul,regular_add,regular_const,true_and]
  refine ⟨⟨regular_pow A 2 (regular_A q),regular_pow ρ 2 (regular_ρ q)⟩,?_⟩
  simp only [eval_mul,eval_add,eval_const,eval_pow,eval_A,eval_ρ]
  positivity
lemma Z_regular {c : ℝ} (hc : 0<c) {q : Dom} (hq : 0<q.2) : (Z c).RegularAt q := by
  simp only [Z,regular_sqrt,regular_mul,regular_add,regular_const,true_and]
  refine ⟨⟨regular_pow A 2 (regular_A q),regular_pow ρ 2 (regular_ρ q),regular_s q⟩,?_⟩
  simp only [eval_mul,eval_add,eval_const,eval_pow,eval_A,eval_ρ,eval_s]
  positivity
lemma regular {a : Fin 6 → ℝ} {c : ℝ} (hc : 0<c) {q : Dom} (hq : 0<q.2) :
    (Expr a c).RegularAt q := by
  have hx := X_regular hc q
  have hz := Z_regular hc hq
  have hxp := X_pos hc q
  have hzp := Z_pos hc hq
  have hsum : (Z c+X c).RegularAt q := ⟨hz,hx⟩
  have hsp : 0<(Z c+X c).eval q := by simpa only [eval_add] using add_pos hzp hxp
  have hp (e : AlgebraicExpr Dom) (n : ℕ) (he : e.RegularAt q) := regular_pow e n he
  simp only [Expr,K,B,η,Rem,C₁,C₂,C₃,C₄,Δ,regular_add,regular_mul,regular_div,
    regular_sub,regular_neg,regular_const,regular_ρ,regular_ε,regular_s,
    true_and,hx,hz,hp,eval_mul,eval_const,eval_pow,eval_add]
  repeat' constructor
  all_goals first | assumption | positivity
lemma analytic {a : Fin 6 → ℝ} {c : ℝ} (hc : 0<c) {q : Dom} (hq : 0<q.2) :
    ContDiffAt ℝ ω (Φ a c) q := (Expr a c).eval_analytic (regular hc hq)
lemma local_flow (a : Fin 6 → ℝ) {c : ℝ} (hc : 0<c) (x : State Params) (hx : 0<x.2.1) :
    ∃ f : State Params × ℝ → State Params, ContDiffAt ℝ ω f (x,0) ∧
      ∀ᶠ q in 𝓝 (x,(0:ℝ)), f (q.1,0)=q.1 ∧
        HasDerivAt (fun s => f (q.1,s)) (field (Φ a c) (f q)) q.2 :=
  algebraic_profile_flow (Expr a c) x (regular hc hx)
lemma base_zero (a : Fin 6 → ℝ) (c : ℝ) (p : Params) : Φ a c (p,1)=0 := by
  simp [Φ,Expr,η]
lemma rho_zero (a : Fin 6 → ℝ) (c u x : ℝ) : Φ a c (((u,0),0),x)=0 := by
  simp [Φ,Expr]
end QuinticLienard.ScaledProfile

end OAI
