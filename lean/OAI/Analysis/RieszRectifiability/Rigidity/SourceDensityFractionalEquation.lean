import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.SourceDensityRieszEquation
import OAI.Analysis.RieszRectifiability.Foundations.DensityGradientEquation

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Set Filter Topology
open scoped NNReal ENNReal

theorem source_planar_density_fractional_equation {d : ℕ} (p : ℕ) (C G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hgrowth : ∀ j, GlobalUpperGrowth (p + 1) C (μ j))
    (hgν : GlobalUpperGrowth (p + 1) G ν) (hweak : CompactTestConvergence μ ν)
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ u : Ambient d → ℝ, MemLp u 2 (μ j) →
      MemLp (truncated (p + 1) (μ j) ε u) 2 (μ j) ∧
        eLpNorm (truncated (p + 1) (μ j) ε u) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm u 2 (μ j))
    (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (f : Ambient (p + 1) → ℝ)
    (hf : Measurable f) (c : ℝ) (hc : 0 < c) (hlower : ∀ x, c ≤ f x)
    (M : ℝ) (hupper : ∀ x, |f x| ≤ M)
    (hdensity : ((volume : Measure (Ambient (p + 1))).withDensity
      (fun x => ENNReal.ofReal (f x))).map L = ν)
    (a : Ambient (p + 1)) (H R : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hboundary : ν (frontier (ball (L a) R)) = 0) (hmass : ν (ball (L a) R) ≠ 0)
    (cMass : ℝ) (hcMass : 0 < cMass)
    (hlowerMass : ENNReal.ofReal (cMass * (H / 4) ^ (p + 1)) ≤ ν (ball (L a) (H / 4)))
    (hreflect : ScalarReflectionlessAt (p + 1) ν (L a))
    (ψ : 𝓢(Ambient (p + 1), ℝ)) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ ball a H) :
    Integrable (fun y => f y * ((-1 / 2 : ℝ) * ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) volume ∧
      (∫ y, f y * ((-1 / 2 : ℝ) * ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) = 0 := by
  apply density_fractional_equation_of_riesz_tests p f ψ
  intro e
  obtain ⟨_, _, hDs, _, hmean⟩ :=
    compact_smooth_directional_derivative_test ψ (ψ.smooth ⊤) hψc e
  have hsupport : ∀ x, scalarSchwartzDerivative ψ e x ≠ 0 → x ∈ ball a H := by
    intro x hx
    exact hψs (hDs (subset_tsupport (fun y => fderiv ℝ ψ y e) hx))
  exact source_planar_density_riesz_test_equation p C G μ ν hgrowth hgν hweak D hB
    L f hf c hc hlower M hupper hdensity e a H R hH hR hHR hboundary hmass cMass hcMass
    hlowerMass hreflect (scalarSchwartzDerivative ψ e) hmean hsupport

end

end RieszRectifiability

end OAI
