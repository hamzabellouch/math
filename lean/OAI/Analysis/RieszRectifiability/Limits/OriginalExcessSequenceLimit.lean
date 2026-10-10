import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.ExcessSourcePlaneMoments
import OAI.Analysis.RieszRectifiability.Limits.DyadicSourceExcessLimit

namespace OAI

/-!
# Vanishing normalized excess for the original sequence

Dyadic excess bounds yield fixed-plane source moments after a finite index shift.
Applying the source-excess limit theorem to that tail, then restoring the shift,
produces a strictly increasing subsequence with vanishing normalized excess at
every nonnegative radius.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem exists_original_excess_sequence_limit {p d : ℕ} (hnd : p + 1 ≤ d)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (μ j) (ball x r))
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support)
    (δ : ℕ → ℝ) (T : ℕ → ℕ) (hδ : Tendsto δ atTop (𝓝 0)) (hT : Tendsto T atTop atTop)
    (hδpos : ∀ j, 0 < δ j)
    (horizon : ∀ j, AdmissibleRadius (μ j) ((2 : ℝ) ^ T j))
    (b : ℝ) (hb1 : 1 < b) (hb2 : b < 2)
    (hsmall : Tendsto (fun j => δ j * b ^ T j) atTop (𝓝 0))
    (hexcess : ∀ j l, l ≤ T j →
      squaredExcess (p + 1) (μ j) 0 ((2 : ℝ) ^ l) ≤ (δ j * b ^ l) ^ 2)
    (A : ℕ → ℝ) (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) 0 (A j) (δ j ^ 3))
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ u : Ambient d → ℝ, MemLp u 2 (μ j) →
      MemLp (truncated (p + 1) (μ j) ε u) 2 (μ j) ∧
        eLpNorm (truncated (p + 1) (μ j) ε u) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm u 2 (μ j))
    (hlast : Tendsto (fun j => ((2 : ℝ) ^ T j)⁻¹ / δ j) atTop (𝓝 0)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∀ r : ℝ, 0 ≤ r →
      Tendsto (fun j => squaredExcess (p + 1) (μ (ρ j)) 0 r / δ (ρ j) ^ 2) atTop (𝓝 0) := by
  obtain ⟨J, M, _hM, S, hS, hmoment⟩ := exists_shifted_fixed_plane_source_moments hnd
    μ C G hC hg (fun j r hr => hlower j 0 (hzero j) r hr)
    δ hδpos T horizon b hb1 hsmall hexcess
  have hshift : Tendsto (fun j : ℕ => j + J) atTop atTop := tendsto_add_atTop_nat J
  have hdiam := support_diameters_grow_of_admissible_dyadic_horizon μ T hT horizon
  obtain ⟨ρ, hρ, hlim⟩ := exists_dyadic_source_excess_limit (fun j => μ (j + J)) C G hC
    (fun j => hg (j + J)) (fun j => hlower (j + J))
    (fun r hr => hshift.eventually (hdiam r hr)) (fun j => hzero (j + J)) S hS
    (fun j => δ (j + J)) (fun j => T (j + J)) (hδ.comp hshift) (hT.comp hshift)
    M b hmoment (fun j => A (j + J)) (hA.comp hshift) (fun j => hosc (j + J))
    D (fun j => hB (j + J)) (fun j => hδpos (j + J)) hb1.le hb2 (hlast.comp hshift)
  refine ⟨fun j => ρ j + J, ?_, hlim⟩
  intro i j hij
  exact Nat.add_lt_add_right (hρ hij) J

end

end RieszRectifiability

end OAI
