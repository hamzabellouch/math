import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.FlatSeedExcess

namespace OAI

/-!
# Propagation from a flat seed

A thin support tube supplies the initial excess bounds for a dyadic chain.
Uniformly small scalar oscillation propagates those bounds and bilateral
flatness to its descendants. Conversely, a bad descendant scale provides a
mean-zero Lipschitz test with a large scalar Riesz pairing at an earlier scale.
The propagation parameters are chosen before the measure and the seed ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_uniform_flat_seed_chain_propagation {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (hC : 0 < C) (hG : 0 ≤ G) (b : ℝ) (hb1 : 1 < b) (hb2 : b ^ 2 < 2)
    (D : ℝ≥0) (ε : ℝ) (hε : 0 < ε) (J₀ : ℕ) :
    ∃ J : ℕ, J₀ ≤ J ∧ ∃ α : ℝ, 0 < α ∧ α ≤ propagationScale J ∧
      ∀ μ : Measure (Ambient d), GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ s : ℝ, AdmissibleRadius μ s →
        ENNReal.ofReal (s ^ (p + 1) / C) ≤ μ (ball x s)) →
      ∀ a ∈ μ.support, ∀ r : ℝ, 0 < r →
      AdmissibleRadius μ (r * (2 : ℝ) ^ propagationHorizon J) →
      (∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane (p + 1) S ∧
        ∀ x ∈ ball a (r * (2 : ℝ) ^ propagationHorizon J), x ∈ μ.support →
          infDist x (S : Set (Ambient d)) ≤ α * r) →
      (∀ η, 0 < η → ∀ u : Ambient d → ℝ, MemLp u 2 μ →
        MemLp (truncated (p + 1) μ η u) 2 μ ∧
          eLpNorm (truncated (p + 1) μ η u) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm u 2 μ) →
      ∀ L : ℕ,
      (∀ j < L, ScalarOscillationBound (p + 1) μ a
        (descendantRadius r j * propagationTestRadius J)
        (descendantRadius r j ^ (p + 2) * propagationScale J ^ 3)) →
      ∀ j ≤ L,
        squaredExcess (p + 1) μ a (descendantRadius r j) ≤ propagationScale J ^ 2 ∧
        (0 < j → bilateralBeta (p + 1) μ a (descendantRadius r j) < ε) := by
  obtain ⟨J, hJ₀, hJ⟩ := exists_uniform_dyadic_chain_propagation hnd C G hC b hb1 hb2 D ε hε J₀
  obtain ⟨α, hα, hαδ, hsmall⟩ := exists_positive_tube_threshold G (propagationScale J) hG
    (propagationScale_pos J)
  refine ⟨J, hJ₀, α, hα, hαδ, ?_⟩
  intro μ hg hlower a ha r hr horizon htube hB L hosc
  obtain ⟨S, hS, hs⟩ := htube
  have hinit := initial_excess_horizon_of_support_tube (p + 1) G μ hg a r α (propagationScale J) b
    hr hα.le (propagationScale_pos J).le hb1.le hsmall (propagationHorizon J) S hS hs
  exact hJ μ hg hlower a ha r hr horizon hinit hB L hosc

theorem exists_uniform_flat_seed_bad_scale_witness {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (hC : 0 < C) (hG : 0 ≤ G) (b : ℝ) (hb1 : 1 < b) (hb2 : b ^ 2 < 2)
    (D : ℝ≥0) (ε : ℝ) (hε : 0 < ε) (J₀ : ℕ) :
    ∃ J : ℕ, J₀ ≤ J ∧ ∃ α : ℝ, 0 < α ∧ α ≤ propagationScale J ∧
      ∀ μ : Measure (Ambient d), GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ s : ℝ, AdmissibleRadius μ s →
        ENNReal.ofReal (s ^ (p + 1) / C) ≤ μ (ball x s)) →
      ∀ a ∈ μ.support, ∀ r : ℝ, 0 < r →
      AdmissibleRadius μ (r * (2 : ℝ) ^ propagationHorizon J) →
      (∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane (p + 1) S ∧
        ∀ x ∈ ball a (r * (2 : ℝ) ^ propagationHorizon J), x ∈ μ.support →
          infDist x (S : Set (Ambient d)) ≤ α * r) →
      (∀ η, 0 < η → ∀ u : Ambient d → ℝ, MemLp u 2 μ →
        MemLp (truncated (p + 1) μ η u) 2 μ ∧
          eLpNorm (truncated (p + 1) μ η u) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm u 2 μ) →
      ∀ L : ℕ, 0 < L → ε ≤ bilateralBeta (p + 1) μ a (descendantRadius r L) →
      ∃ j < L, ∃ e : Ambient d, ‖e‖ ≤ 1 ∧ ∃ φ : Ambient d → ℝ,
        LipschitzWith 1 φ ∧ tsupport φ ⊆ ball a (descendantRadius r j * propagationTestRadius J) ∧
        (∫ x, φ x ∂μ) = 0 ∧
        descendantRadius r j ^ (p + 2) * propagationScale J ^ 3 <
          |rieszScalarPairing (p + 1) μ a (2 * (descendantRadius r j * propagationTestRadius J)) e φ| := by
  classical
  obtain ⟨J, hJ₀, α, hα, hαδ, hJ⟩ :=
    exists_uniform_flat_seed_chain_propagation hnd C G hC hG b hb1 hb2 D ε hε J₀
  refine ⟨J, hJ₀, α, hα, hαδ, ?_⟩
  intro μ hg hlower a ha r hr horizon htube hB L hL hbad
  have hnot : ¬ (∀ j < L, ScalarOscillationBound (p + 1) μ a
      (descendantRadius r j * propagationTestRadius J)
      (descendantRadius r j ^ (p + 2) * propagationScale J ^ 3)) := by
    intro hosc
    have hgood := hJ μ hg hlower a ha r hr horizon htube hB L hosc L le_rfl
    exact (not_lt_of_ge hbad) (hgood.2 hL)
  push Not at hnot
  obtain ⟨j, hj, hfail⟩ := hnot
  unfold ScalarOscillationBound at hfail
  push Not at hfail
  obtain ⟨e, he, φ, hφ, hs, hzero, hlarge⟩ := hfail
  exact ⟨j, hj, e, he, φ, hφ, hs, hzero, hlarge⟩

end

end RieszRectifiability

end OAI
