import OAI.NumberTheory.Ostmann.Construction.LogCellPNT

namespace OAI

open Filter
open scoped Topology
namespace Ostmann.Construction

theorem eventually_theta_relative_error {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, |Chebyshev.theta x-x| ≤ ε*x := by
  have h := Metric.tendsto_nhds.mp tendsto_theta_ratio ε hε
  filter_upwards [h, eventually_gt_atTop (0:ℝ)] with x hx hx0
  have heq : Chebyshev.theta x/x-1 = (Chebyshev.theta x-x)/x := by field_simp
  rw [Real.dist_eq, heq, abs_div, abs_of_pos hx0] at hx
  exact ((div_lt_iff₀ hx0).mp hx).le

end Ostmann.Construction

end OAI
