import OAI.MeasureTheory.Falconer.Angular.InverseStationaryOperators
import Mathlib.Algebra.BigOperators.Intervals

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

theorem inverseStationaryOperator_triangle (n : ℕ) (z : ℂ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    (∑ h ∈ Finset.range (n+1), ∑ j ∈ Finset.range (n+1-h),
      z^(h+j) * directStationaryOperator h (inverseStationaryOperator j f) x) = f x := by
  rw [← Finset.sum_range_diag_flip]
  have he : ∀ k ∈ Finset.range (n+1),
      (∑ h ∈ Finset.range (k+1),
        z^(h+(k-h)) * directStationaryOperator h (inverseStationaryOperator (k-h) f) x) =
          z^k * (if k = 0 then f x else 0) := by
    intro k hk
    rw [← inverseStationaryOperator_cancellation k hf x, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    have hh' : h ≤ k := by have := Finset.mem_range.mp hh; omega
    rw [Nat.add_sub_of_le hh']
  rw [Finset.sum_congr rfl he]
  simp

theorem inverseStationaryOperator_composed_bound (h j : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (x : ℝ)
    (hb : ∀ k ≤ 2*(h+j), ‖iteratedDeriv k f x‖ ≤ C*D^k) :
    ‖directStationaryOperator h (inverseStationaryOperator j f) x‖ ≤
      (directStationaryExpr h).cost * (inverseStationaryExpr j).cost *
        (C*D^(2*(h+j))) := by
  have ho : (AngularDifferentialExpr.comp (directStationaryExpr h)
      (inverseStationaryExpr j)).order ≤ 2*(h+j) := by
    have := directStationaryExpr_order h
    have := inverseStationaryExpr_order j
    change _ + _ ≤ _
    omega
  have he := (AngularDifferentialExpr.comp (directStationaryExpr h)
    (inverseStationaryExpr j)).derivative_bound_of_order_le ho hf hC hD 0 x (by simpa using hb)
  simpa only [iteratedDeriv_zero, AngularDifferentialExpr.apply,
    directStationaryExpr_apply, AngularDifferentialExpr.cost, zero_add,
    inverseStationaryOperator] using he

end PlanarFalconer

end OAI
