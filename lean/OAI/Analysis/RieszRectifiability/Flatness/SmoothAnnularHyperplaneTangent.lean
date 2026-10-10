import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.SmoothAnnularNormalPotential
import OAI.Analysis.RieszRectifiability.Flatness.NormalHyperplaneTangent

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem exists_nonzero_smooth_annular_hyperplane_tangent {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ n / C) ≤ μ (ball x R))
    (hzero : (0 : Ambient d) ∈ μ.support)
    (e : Ambient d) (he : e ≠ 0) (hside : ∀ x ∈ μ.support, 0 ≤ inner ℝ e x)
    (R₀ B : ℝ) (hR₀ : 0 < R₀)
    (hB : ∀ (r : ℝ) (hr : 0 < r), 2 * r ≤ R₀ →
      ‖smoothAnnularTransform n μ 0 r R₀ hr hR₀‖ ≤ B)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hr0 : Tendsto r atTop (𝓝 0)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
      CompactTestConvergence (fun j => blowupMeasure n μ 0 (r (ρ j))) ν ∧
      GlobalUpperGrowth n (G * 2 ^ n) ν ∧ (0 : Ambient d) ∈ ν.support ∧
      (∀ x ∈ ν.support, ∀ R : ℝ, 0 < R →
        ENNReal.ofReal (R ^ n / (C * 4 ^ n)) ≤ ν (ball x R)) ∧
      (∀ x ∈ ν.support, inner ℝ e x = 0) ∧ e ∉ ν.support := by
  have hpotential := positiveNormalPotential_truncated_bound_of_smooth_annuli n hn G μ hg
    e hside R₀ B hR₀ hB
  obtain ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, hzeroν, hlowerν, hplane⟩ :=
    exists_nonzero_normal_hyperplane_tangent n (by omega) μ C G hC hg hlower hzero e hside
      R₀ (‖e‖ * B) hR₀ hpotential r hr hr0
  refine ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, hzeroν, hlowerν, hplane, ?_⟩
  intro hesupp
  have hz := hplane e hesupp
  rw [real_inner_self_eq_norm_sq] at hz
  have hp := norm_pos_iff.mpr he
  nlinarith

end

end RieszRectifiability

end OAI
