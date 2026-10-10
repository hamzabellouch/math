import OAI.MeasureTheory.Falconer.Angular.AngularDifferentialExpr
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology
namespace AngularDifferentialExpr

theorem smooth_finite {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (m : ℕ) (x : ℝ) :
    ContDiffAt ℝ m f x :=
  (hf.of_le (WithTop.coe_le_coe.mpr (show (m:ℕ∞) ≤ ⊤ from le_top))).contDiffAt

theorem derivative_bound (p : AngularDifferentialExpr) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D)
    (m : ℕ) (x : ℝ)
    (hb : ∀ k ≤ m+p.order, ‖iteratedDeriv k f x‖ ≤ C*D^k) :
    ‖iteratedDeriv m (p.apply f) x‖ ≤ p.cost * (C*D^(m+p.order)) := by
  induction p generalizing f C m with
  | term c k =>
    simp only [apply, cost, order, iteratedDeriv_const_mul_field, iteratedDeriv_iterated,
      norm_mul]
    exact mul_le_mul_of_nonneg_left (hb (m+k) le_rfl) (norm_nonneg c)
  | add p q hp hq =>
    have hpord : m+p.order ≤ m+max p.order q.order := Nat.add_le_add_left (le_max_left _ _) _
    have hqord : m+q.order ≤ m+max p.order q.order := Nat.add_le_add_left (le_max_right _ _) _
    have hp' := hp hf hC m (fun k hk => hb k (hk.trans hpord))
    have hq' := hq hf hC m (fun k hk => hb k (hk.trans hqord))
    change ‖iteratedDeriv m (fun y => p.apply f y + q.apply f y) x‖ ≤ _
    rw [iteratedDeriv_fun_add (smooth_finite (p.apply_contDiff hf) m x)
      (smooth_finite (q.apply_contDiff hf) m x)]
    apply (norm_add_le _ _).trans
    calc
      _ ≤ p.cost * (C*D^(m+max p.order q.order)) +
          q.cost * (C*D^(m+max p.order q.order)) := add_le_add
        (hp'.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hpord) hC) p.cost_nonneg))
        (hq'.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hqord) hC) q.cost_nonneg))
      _ = _ := by simp only [cost, order]; ring
  | comp p q hp hq =>
    have hCq : 0 ≤ q.cost*C*D^q.order := by
      exact mul_nonneg (mul_nonneg q.cost_nonneg hC) (pow_nonneg (zero_le_one.trans hD) _)
    have hbq : ∀ k ≤ m+p.order,
        ‖iteratedDeriv k (q.apply f) x‖ ≤ (q.cost*C*D^q.order)*D^k := by
      intro k hk
      have h := hq hf hC k (fun l hl => hb l (by
        simp only [order]; omega))
      apply h.trans_eq
      rw [pow_add]
      ring
    have h := hp (q.apply_contDiff hf) hCq m hbq
    apply h.trans_eq
    simp only [cost, order, pow_add]
    ring

theorem derivative_bound_of_order_le (p : AngularDifferentialExpr) {n : ℕ}
    (hn : p.order ≤ n) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (m : ℕ) (x : ℝ)
    (hb : ∀ k ≤ m+n, ‖iteratedDeriv k f x‖ ≤ C*D^k) :
    ‖iteratedDeriv m (p.apply f) x‖ ≤ p.cost * (C*D^(m+n)) := by
  have hm := Nat.add_le_add_left hn m
  exact (p.derivative_bound hf hC hD m x (fun k hk => hb k (hk.trans hm))).trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hm) hC) p.cost_nonneg)

theorem iteratedDeriv_tsupport (k : ℕ) (f : ℝ → ℂ) :
    tsupport (iteratedDeriv k f) ⊆ tsupport f := by
  induction k with
  | zero => simp
  | succ k ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

theorem apply_tsupport (p : AngularDifferentialExpr) (f : ℝ → ℂ) :
    tsupport (p.apply f) ⊆ tsupport f := by
  induction p generalizing f with
  | term c k => exact tsupport_mul_subset_right.trans (iteratedDeriv_tsupport k f)
  | add p q hp hq => exact (tsupport_add (p.apply f) (q.apply f)).trans (Set.union_subset (hp f) (hq f))
  | comp p q hp hq => exact (hp (q.apply f)).trans (hq f)

end AngularDifferentialExpr
end PlanarFalconer

end OAI
