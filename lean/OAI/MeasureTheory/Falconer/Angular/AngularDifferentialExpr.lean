import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.Basic

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology

inductive AngularDifferentialExpr where
  | term (coefficient : ℂ) (order : ℕ)
  | add (p q : AngularDifferentialExpr)
  | comp (p q : AngularDifferentialExpr)

namespace AngularDifferentialExpr

def order : AngularDifferentialExpr → ℕ
  | .term _ k => k
  | .add p q => max p.order q.order
  | .comp p q => p.order + q.order

noncomputable def apply : AngularDifferentialExpr → (ℝ → ℂ) → (ℝ → ℂ)
  | .term c k, f => fun x => c * iteratedDeriv k f x
  | .add p q, f => fun x => p.apply f x + q.apply f x
  | .comp p q, f => p.apply (q.apply f)

noncomputable def cost : AngularDifferentialExpr → ℝ
  | .term c _ => ‖c‖
  | .add p q => p.cost + q.cost
  | .comp p q => p.cost * q.cost

theorem cost_nonneg (p : AngularDifferentialExpr) : 0 ≤ p.cost := by
  induction p with
  | term c k => exact norm_nonneg c
  | add p q hp hq => exact add_nonneg hp hq
  | comp p q hp hq => exact mul_nonneg hp hq

theorem smooth_iteratedDeriv {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv k f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2

theorem apply_contDiff (p : AngularDifferentialExpr) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (p.apply f) := by
  induction p generalizing f with
  | term c k => exact contDiff_const.mul (smooth_iteratedDeriv hf k)
  | add p q hp hq => exact (hp hf).add (hq hf)
  | comp p q hp hq => exact hp (hq hf)

theorem iteratedDeriv_iterated (m k : ℕ) (f : ℝ → ℂ) :
    iteratedDeriv m (iteratedDeriv k f) = iteratedDeriv (m+k) f := by
  simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

theorem apply_germ (p : AngularDifferentialExpr) {f g : ℝ → ℂ} {x : ℝ}
    (h : f =ᶠ[𝓝 x] g) : p.apply f =ᶠ[𝓝 x] p.apply g := by
  induction p generalizing f g with
  | term c k =>
    filter_upwards [h.iteratedDeriv k] with y hy
    exact congrArg (c * ·) hy
  | add p q hp hq => exact (hp h).add (hq h)
  | comp p q hp hq => exact hp (hq h)

theorem apply_zero (p : AngularDifferentialExpr) : p.apply (fun _ => 0) = fun _ => 0 := by
  induction p with
  | term c k => funext x; simp [apply]
  | add p q hp hq => simp [apply, hp, hq]
  | comp p q hp hq => simpa only [apply, hq] using hp

def sum : List AngularDifferentialExpr → AngularDifferentialExpr
  | [] => .term 0 0
  | p :: ps => .add p (sum ps)

theorem sum_apply (ps : List AngularDifferentialExpr) (f : ℝ → ℂ) (x : ℝ) :
    (sum ps).apply f x = (ps.map (fun p => p.apply f x)).sum := by
  induction ps with
  | nil => simp [sum, apply]
  | cons p ps ih => simp [sum, apply, ih]

theorem sum_order_le (ps : List AngularDifferentialExpr) (n : ℕ)
    (h : ∀ p ∈ ps, p.order ≤ n) : (sum ps).order ≤ n := by
  induction ps with
  | nil => exact Nat.zero_le n
  | cons p ps ih =>
    exact max_le (h p (by simp)) (ih (fun q hq => h q (by simp [hq])))

end AngularDifferentialExpr
end PlanarFalconer

end OAI
