import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactSupportApproximants
import OAI.Analysis.RieszRectifiability.Limits.SmoothAnnularCenterLimits

namespace OAI

/-!
# Annular transform bounds on limiting supports

Support-point approximants and moving-center convergence transfer eventual
uniform smooth annular bounds to support points of a weak limit inside an open set.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem smoothAnnularTransform_bound_at_limit_support {d : ℕ} (n : ℕ) (G B : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts ν] (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (hlocal : CompactTestConvergence μ ν) (U : Set (Ambient d)) (hU : IsOpen U)
    (b : Ambient d) (hbs : b ∈ ν.support) (hbU : b ∈ U)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (hb : ∀ᶠ j in atTop, ∀ x ∈ (μ j).support, x ∈ U →
      ‖smoothAnnularTransform n (μ j) x r R hr (hr.trans_le hrR)‖ ≤ B) :
    ‖smoothAnnularTransform n ν b r R hr (hr.trans_le hrR)‖ ≤ B := by
  let (j : ℕ) : IsFiniteMeasureOnCompacts (μ j) := globalGrowth_finite_on_compacts G (μ j) (hg j)
  obtain ⟨φ, a, _, hφ, has, ha⟩ := compactTestConvergence_support_approximants μ ν hlocal b hbs
  have hc : CompactTestConvergence (μ ∘ φ) ν := fun f => (hlocal f).comp hφ
  apply smoothAnnularTransform_bound_of_center_limit n G B (μ ∘ φ) ν
    (fun j => hg (φ j)) hc a b ha r R hr hrR
  filter_upwards [hφ.eventually hb, ha.eventually (hU.mem_nhds hbU)] with j hj hja
  exact hj (a j) (has j) hja

end

end RieszRectifiability

end OAI
