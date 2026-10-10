import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.UniformNonflatTangents
import OAI.Analysis.RieszRectifiability.Foundations.AnnularBoundedTangents

namespace OAI

/-!
# Nonflat hyperplane tangents with annular bounds

The hyperplane tangent construction retains both the global smooth annular bound and
a quantitative bilateral nonflatness bound. The latter passes through tangent formation
with the explicit loss from `ε` to `ε / 64`.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem exists_nonflat_annular_hyperplane_tangent {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (μ : Measure (Ambient d)) (C G B ε : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ n / C) ≤ μ (ball x R))
    (hzero : (0 : Ambient d) ∈ μ.support) (hB : GlobalSmoothAnnularBound n μ B)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hbad : GlobalBilateralLower n μ ε)
    (e : Ambient d) (he : e ≠ 0) (hside : ∀ x ∈ μ.support, 0 ≤ inner ℝ e x)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hr0 : Tendsto r atTop (𝓝 0)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
      CompactTestConvergence (fun j => blowupMeasure n μ 0 (r (ρ j))) ν ∧
      GlobalUpperGrowth n (G * 2 ^ n) ν ∧ (0 : Ambient d) ∈ ν.support ∧
      (∀ x ∈ ν.support, ∀ R : ℝ, 0 < R →
        ENNReal.ofReal (R ^ n / (C * 4 ^ n)) ≤ ν (ball x R)) ∧
      (∀ x ∈ ν.support, inner ℝ e x = 0) ∧ e ∉ ν.support ∧
      GlobalSmoothAnnularBound n ν B ∧ GlobalBilateralLower n ν (ε / 64) := by
  obtain ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, hzeroν, hlowerν, hplane, hproper, hBν⟩ :=
    exists_annular_bounded_hyperplane_tangent n hn μ C G B hC hg hlower hzero hB
      e he hside r hr hr0
  let := hfinite
  refine ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, hzeroν, hlowerν, hplane, hproper, hBν, ?_⟩
  exact GlobalBilateralLower.tangent hn hnd μ ν C G hC hg hlower 0 hzero
    (fun j => r (ρ j)) (fun j => hr (ρ j)) hlocal ε hε hε1 hbad

end

end RieszRectifiability

end OAI
