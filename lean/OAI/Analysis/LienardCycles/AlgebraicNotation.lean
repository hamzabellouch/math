import OAI.Analysis.LienardCycles.AlgebraicFlow

namespace OAI

universe uE

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.SmoothFlow.AlgebraicExpr
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
instance : Add (AlgebraicExpr E) := ⟨add⟩
instance : Mul (AlgebraicExpr E) := ⟨mul⟩
instance : Inv (AlgebraicExpr E) := ⟨inv⟩
instance : Neg (AlgebraicExpr E) := ⟨fun p => mul (const (-1)) p⟩
instance : Sub (AlgebraicExpr E) := ⟨fun p q => p + -q⟩
instance : Div (AlgebraicExpr E) := ⟨fun p q => p*q⁻¹⟩
instance (n : ℕ) : OfNat (AlgebraicExpr E) n := ⟨const n⟩
def pow (p : AlgebraicExpr E) : ℕ → AlgebraicExpr E
 | 0 => const 1
 | n+1 => pow p n*p
instance : Pow (AlgebraicExpr E) ℕ := ⟨pow⟩
@[simp] lemma eval_const (c : ℝ) (x : E) : (const c : AlgebraicExpr E).eval x=c := rfl
@[simp] lemma eval_linear (L : E →L[ℝ] ℝ) (x : E) : (linear L).eval x=L x := rfl
@[simp] lemma eval_add (p q : AlgebraicExpr E) (x : E) : (p+q).eval x=p.eval x+q.eval x := rfl
@[simp] lemma eval_mul (p q : AlgebraicExpr E) (x : E) : (p*q).eval x=p.eval x*q.eval x := rfl
@[simp] lemma eval_inv (p : AlgebraicExpr E) (x : E) : p⁻¹.eval x=(p.eval x)⁻¹ := rfl
@[simp] lemma eval_neg (p : AlgebraicExpr E) (x : E) : (-p).eval x= -p.eval x := by change (-1:ℝ)*p.eval x= -p.eval x; ring
@[simp] lemma eval_sub (p q : AlgebraicExpr E) (x : E) : (p-q).eval x=p.eval x-q.eval x := by change (p+ -q).eval x=_; rw [eval_add,eval_neg,sub_eq_add_neg]
@[simp] lemma eval_div (p q : AlgebraicExpr E) (x : E) : (p/q).eval x=p.eval x/q.eval x := by change (p*q⁻¹).eval x=_; rw [eval_mul,eval_inv,div_eq_mul_inv]
@[simp] lemma eval_ofNat (n : ℕ) (x : E) : (OfNat.ofNat n : AlgebraicExpr E).eval x=n := rfl
@[simp] lemma eval_pow (p : AlgebraicExpr E) (n : ℕ) (x : E) : (p^n).eval x=(p.eval x)^n := by
  induction n with
  | zero =>
    rw [pow_zero]
    change (pow p 0).eval x=1
    rfl
  | succ n ih => change (p^n).eval x*p.eval x=_; rw [ih,pow_succ]
@[simp] lemma eval_sqrt (p : AlgebraicExpr E) (x : E) : (sqrt p).eval x=Real.sqrt (p.eval x) := rfl
@[simp] lemma regular_const (c : ℝ) (x : E) : (const c : AlgebraicExpr E).RegularAt x := trivial
@[simp] lemma regular_linear (L : E →L[ℝ] ℝ) (x : E) : (linear L).RegularAt x := trivial
@[simp] lemma regular_add (p q : AlgebraicExpr E) (x : E) : (p+q).RegularAt x ↔ p.RegularAt x ∧ q.RegularAt x := Iff.rfl
@[simp] lemma regular_mul (p q : AlgebraicExpr E) (x : E) : (p*q).RegularAt x ↔ p.RegularAt x ∧ q.RegularAt x := Iff.rfl
@[simp] lemma regular_inv (p : AlgebraicExpr E) (x : E) : p⁻¹.RegularAt x ↔ p.RegularAt x ∧ p.eval x≠0 := Iff.rfl
@[simp] lemma regular_neg (p : AlgebraicExpr E) (x : E) : (-p).RegularAt x ↔ p.RegularAt x := by change (True ∧ p.RegularAt x) ↔ p.RegularAt x; simp
@[simp] lemma regular_sub (p q : AlgebraicExpr E) (x : E) : (p-q).RegularAt x ↔ p.RegularAt x ∧ q.RegularAt x := by change (p+ -q).RegularAt x ↔ _; rw [regular_add,regular_neg]
@[simp] lemma regular_div (p q : AlgebraicExpr E) (x : E) : (p/q).RegularAt x ↔ p.RegularAt x ∧ q.RegularAt x ∧ q.eval x≠0 := Iff.rfl
@[simp] lemma regular_ofNat (n : ℕ) (x : E) : (OfNat.ofNat n : AlgebraicExpr E).RegularAt x := trivial
lemma regular_pow (p : AlgebraicExpr E) (n : ℕ) {x : E} (hp : p.RegularAt x) : (p^n).RegularAt x := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ih,hp⟩
@[simp] lemma regular_sqrt (p : AlgebraicExpr E) (x : E) : (sqrt p).RegularAt x ↔ p.RegularAt x ∧ 0<p.eval x := Iff.rfl
end QuinticLienard.SmoothFlow.AlgebraicExpr

end OAI
