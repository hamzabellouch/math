import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.BlowupBilateralBeta
import OAI.Analysis.RieszRectifiability.Foundations.UniformBilateralExcessPropagation
import OAI.Analysis.RieszRectifiability.Foundations.BlowupExcess
import OAI.Analysis.RieszRectifiability.Foundations.BlowupOscillation

namespace OAI

/-!
# Scale-invariant bilateral excess propagation

Blowing up at a support point and a positive radius reduces excess propagation to its
normalized form. Growth, admissibility, oscillation, and the uniform Riesz bound transfer to
the blowup, while excess and bilateral beta transform back to the original scale.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_scale_invariant_bilateral_excess_propagation {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (hC : 0 < C) (b : ℝ) (hb1 : 1 < b) (hb2 : b ^ 2 < 2)
    (D : ℝ≥0) (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) (J₀ : ℕ) :
    ∃ J : ℕ, J₀ ≤ J ∧ ∀ μ : Measure (Ambient d),
      GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ s : ℝ, AdmissibleRadius μ s →
        ENNReal.ofReal (s ^ (p + 1) / C) ≤ μ (ball x s)) →
      ∀ a ∈ μ.support, ∀ r : ℝ, 0 < r →
      AdmissibleRadius μ (r * (2 : ℝ) ^ propagationHorizon J) →
      (∀ l ≤ propagationHorizon J,
        squaredExcess (p + 1) μ a (r * (2 : ℝ) ^ l) ≤ (propagationScale J * b ^ l) ^ 2) →
      ScalarOscillationBound (p + 1) μ a (r * propagationTestRadius J)
        (r ^ (p + 2) * propagationScale J ^ 3) →
      (∀ η, 0 < η → ∀ u : Ambient d → ℝ, MemLp u 2 μ →
        MemLp (truncated (p + 1) μ η u) 2 μ ∧
          eLpNorm (truncated (p + 1) μ η u) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm u 2 μ) →
      squaredExcess (p + 1) μ a (r * R) ≤ propagationScale J ^ 2 ∧
        bilateralBeta (p + 1) μ a (r * R) < ε := by
  obtain ⟨J, hJ₀, hJ⟩ := exists_uniform_bilateral_excess_propagation hnd C G hC b hb1 hb2
    D R ε hR hε J₀
  refine ⟨J, hJ₀, ?_⟩
  intro μ hg hlower a ha r hr horizon hexcess hosc hB
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  let ν := blowupMeasure (p + 1) μ a r
  have hνg : GlobalUpperGrowth (p + 1) G ν := blowupMeasure_growth (p + 1) μ a r G hr hg
  let : IsFiniteMeasureOnCompacts ν := globalGrowth_finite_on_compacts G ν hνg
  have hνlower := blowupMeasure_lower_admissible (p + 1) μ a r C hr hlower
  have hνzero := blowupMeasure_origin_mem_support (p + 1) μ a r hr ha
  have hνhorizon := (blowupMeasure_admissibleRadius_iff (p + 1) μ a r
    ((2 : ℝ) ^ propagationHorizon J) hr).mpr horizon
  have hνexcess : ∀ l ≤ propagationHorizon J,
      squaredExcess (p + 1) ν 0 ((2 : ℝ) ^ l) ≤ (propagationScale J * b ^ l) ^ 2 := by
    intro l hl
    rw [squaredExcess_blowup (p + 1) μ a r _ hr]
    exact hexcess l hl
  have hνosc := hosc.blowup (p + 1) μ a r (propagationTestRadius J) (propagationScale J ^ 3) hr
  have hνB := uniform_riesz_bound_blowup (p + 1) μ a r hr D hB
  have hresult := hJ ν inferInstance hνg hνlower hνzero hνhorizon hνexcess hνosc hνB
  change squaredExcess (p + 1) (blowupMeasure (p + 1) μ a r) 0 R ≤ propagationScale J ^ 2 ∧
    bilateralBeta (p + 1) (blowupMeasure (p + 1) μ a r) 0 R < ε at hresult
  rwa [squaredExcess_blowup (p + 1) μ a r R hr, bilateralBeta_blowup (p + 1) μ a r R hr] at hresult

end

end RieszRectifiability

end OAI
