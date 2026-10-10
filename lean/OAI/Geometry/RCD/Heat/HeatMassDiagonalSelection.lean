import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # Choose heat indices satisfying value and scaled mass errors together -/

open Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem heat_mass_diagonal_selection (r m B : ℕ → ℝ)
    (value mass : ℕ → ℕ → ℝ) (hr : ∀ k, 0 < r k) (hm : ∀ k, 0 < m k)
    (hvalue : ∀ k, Tendsto (value k) atTop (𝓝 0))
    (hmass : ∀ k η, 0 < η → ∀ᶠ j in atTop, mass k j ≤ B k+η) :
    ∃ j : ℕ → ℕ, (∀ k, k ≤ j k) ∧
      (∀ k, value k (j k) ≤ r k/((k:ℝ)+1)) ∧
      (∀ k, mass k (j k) ≤ B k+m k/((r k)^2*((k:ℝ)+1))) := by
  have hex (k : ℕ) : ∃ j : ℕ, k ≤ j ∧ value k j ≤ r k/((k:ℝ)+1) ∧
      mass k j ≤ B k+m k/((r k)^2*((k:ℝ)+1)) := by
    have hv := Metric.tendsto_nhds.mp (hvalue k) (r k/((k:ℝ)+1))
      (div_pos (hr k) (by positivity))
    have hb := hmass k (m k/((r k)^2*((k:ℝ)+1)))
      (div_pos (hm k) (mul_pos (sq_pos_of_pos (hr k)) (by positivity)))
    obtain ⟨j,hj,hvj,hmj⟩ := ((eventually_ge_atTop k).and (hv.and hb)).exists
    refine ⟨j,hj,?_,hmj⟩
    have hh : |value k j| < r k/((k:ℝ)+1) := by simpa only [Real.dist_eq,sub_zero] using hvj
    exact (le_abs_self _).trans hh.le
  choose j hj hv hm using hex
  exact ⟨j,hj,hv,hm⟩

end RegularPointCoordinates

end

end OAI
