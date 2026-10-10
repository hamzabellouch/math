import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactLimitLowerMass
import OAI.Analysis.RieszRectifiability.Kernel.BoundedBoxHeight
import OAI.Analysis.RieszRectifiability.Limits.OriginalGrowthLimit

namespace OAI

/-!
Compact-test limits retain the original upper growth and lower AD mass bounds along a
subsequence whose support diameters eventually admit every fixed positive radius.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem exists_original_AD_growth_limit {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
      CompactTestConvergence (fun j => μ (ρ j)) ν ∧ GlobalUpperGrowth n (G * 2 ^ n) ν ∧
      ∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
        ENNReal.ofReal (r ^ n / (C * 4 ^ n)) ≤ ν (ball x r) := by
  obtain ⟨c, hc, hmass⟩ := eventual_lower_ball_mass_of_AD_lower n μ C hC hlower hdiam 1 zero_lt_one
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hmass
  have hshift : StrictMono (fun j : ℕ => j + J) := fun _ _ h => Nat.add_lt_add_right h J
  obtain ⟨ρ, hρ, ν, hfinite, hne, hlimit, hgν⟩ := exists_original_growth_limit n
    (fun j => μ (j + J)) G c hc (fun j => hg (j + J))
      (fun j => hJ (j + J) (Nat.le_add_left J j) 0 (hzero (j + J)))
  let := hfinite
  have hρ' : StrictMono (fun j => ρ j + J) := hshift.comp hρ
  refine ⟨(fun j => ρ j + J), hρ', ν, hfinite, hne, hlimit, hgν, ?_⟩
  exact compactTestConvergence_AD_lower n (fun j => μ (ρ j + J)) ν hlimit C hC
    (fun j => hlower (ρ j + J)) (fun r hr => hρ'.tendsto_atTop.eventually (hdiam r hr))

end

end RieszRectifiability

end OAI
