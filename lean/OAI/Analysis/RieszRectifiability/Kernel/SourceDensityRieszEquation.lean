import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.SourcePlanarUnweightedEquation
import OAI.Analysis.RieszRectifiability.Foundations.CappedDensityEquation

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Set Filter Topology
open scoped NNReal ENNReal

theorem source_planar_density_riesz_test_equation {d : ℕ} (p : ℕ) (C G : ℝ)
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
    (e a : Ambient (p + 1)) (H R : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hboundary : ν (frontier (ball (L a) R)) = 0) (hmass : ν (ball (L a) R) ≠ 0)
    (cMass : ℝ) (hcMass : 0 < cMass)
    (hlowerMass : ENNReal.ofReal (cMass * (H / 4) ^ (p + 1)) ≤ ν (ball (L a) (H / 4)))
    (hreflect : ScalarReflectionlessAt (p + 1) ν (L a))
    (g : 𝓢(Ambient (p + 1), ℝ)) (hmean : (∫ y, g y) = 0)
    (hgs : ∀ x, g x ≠ 0 → x ∈ ball a H) :
    Integrable (fun y => f y * scalarRieszSchwartzTest (p + 1) e g y) volume ∧
      (∫ y, f y * scalarRieszSchwartzTest (p + 1) e g y) = 0 := by
  obtain ⟨s, _, hε, b, hEq⟩ := exists_source_planar_unweighted_capped_equation p C G μ ν
    hgrowth hgν hweak D hB L f hf c hc hlower hdensity e a H R hH hR hHR
    hboundary hmass cMass hcMass hlowerMass hreflect
  have htest := hEq g g.continuous.measurable (SchwartzMap.seminorm ℝ 0 0 g)
    (fun x => by simpa only [Real.norm_eq_abs] using! g.norm_le_seminorm ℝ x) g.integrable hgs
  apply density_riesz_test_equation_of_capped_equation p e a H R hH hR hHR f hf M hupper
    g hmean (fun x hx => (hgs x hx).le) (fun j => (1 / 2 : ℝ) ^ (s j))
    (fun _ => pow_pos (by norm_num) _) hε
  simpa only [hmean, mul_zero] using! htest

end

end RieszRectifiability

end OAI
