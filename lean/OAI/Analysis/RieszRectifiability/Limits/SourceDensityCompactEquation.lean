import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.SourceDensityFractionalEquation

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Set Filter Topology
open scoped NNReal ENNReal

theorem source_planar_density_compact_fractional_equation {d : ℕ} (p : ℕ) (C G : ℝ)
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
    (cMass : ℝ) (hcMass : 0 < cMass)
    (hlowerMass : ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (cMass * r ^ (p + 1)) ≤ ν (ball 0 r))
    (hreflect : ScalarReflectionlessAt (p + 1) ν 0)
    (ψ : 𝓢(Ambient (p + 1), ℝ)) (hψc : HasCompactSupport ψ) :
    Integrable (fun y => f y * ((-1 / 2 : ℝ) *
      ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) volume ∧
      (∫ y, f y * ((-1 / 2 : ℝ) *
        ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) = 0 := by
  obtain ⟨H, hH, hψs⟩ := hψc.isBounded.subset_ball_lt 0 (0 : Ambient (p + 1))
  obtain ⟨R, hRi, hboundary⟩ := exists_null_frontier_thickening ν {(0 : Ambient d)}
    (show 2 * H < 2 * H + 1 by linarith)
  simp only [thickening_singleton] at hboundary
  have hR : 0 < R := by linarith [hRi.1]
  have hmass : ν (ball 0 R) ≠ 0 :=
    ((ENNReal.ofReal_pos.mpr (mul_pos hcMass (pow_pos hR _))).trans_le
      (hlowerMass R hR)).ne'
  have hquarter : 0 < H / 4 := by positivity
  apply source_planar_density_fractional_equation p C G μ ν hgrowth hgν hweak D hB
    L f hf c hc hlower M hupper hdensity 0 H R hH hR (le_of_lt hRi.1)
  · simpa only [map_zero] using! hboundary
  · simpa only [map_zero] using! hmass
  · exact hcMass
  · simpa only [map_zero] using! hlowerMass (H / 4) hquarter
  · simpa only [map_zero] using! hreflect
  · exact hψc
  · exact hψs

end

end RieszRectifiability

end OAI
