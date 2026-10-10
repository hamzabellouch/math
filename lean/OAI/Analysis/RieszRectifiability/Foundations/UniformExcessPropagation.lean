import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.OriginalExcessSequenceLimit
import OAI.Analysis.RieszRectifiability.Foundations.ExcessPropagationSchedule

namespace OAI

/-!
# Uniform propagation of small excess

The propagation index is chosen before the measure, for fixed growth, lower
mass, and Riesz bounds. A hypothetical sequence of failures along the schedule
has a subsequence whose normalized excess vanishes at the prescribed radius,
contradicting the lower bound supplied by each failure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem exists_uniform_excess_propagation {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (hC : 0 < C) (b : ℝ) (hb1 : 1 < b) (hb2 : b ^ 2 < 2)
    (D : ℝ≥0) (r : ℝ) (hr : 0 ≤ r) (J₀ : ℕ) :
    ∃ J : ℕ, J₀ ≤ J ∧ ∀ μ : Measure (Ambient d),
      IsFiniteMeasureOnCompacts μ → GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ s : ℝ, AdmissibleRadius μ s →
        ENNReal.ofReal (s ^ (p + 1) / C) ≤ μ (ball x s)) →
      (0 : Ambient d) ∈ μ.support →
      AdmissibleRadius μ ((2 : ℝ) ^ propagationHorizon J) →
      (∀ l ≤ propagationHorizon J,
        squaredExcess (p + 1) μ 0 ((2 : ℝ) ^ l) ≤ (propagationScale J * b ^ l) ^ 2) →
      ScalarOscillationBound (p + 1) μ 0 (propagationTestRadius J) (propagationScale J ^ 3) →
      (∀ ε, 0 < ε → ∀ u : Ambient d → ℝ, MemLp u 2 μ →
        MemLp (truncated (p + 1) μ ε u) 2 μ ∧
          eLpNorm (truncated (p + 1) μ ε u) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm u 2 μ) →
      squaredExcess (p + 1) μ 0 r ≤ propagationScale J ^ 2 := by
  classical
  by_contra h
  push Not at h
  have hbad (j : ℕ) := h (j + J₀) (by omega)
  choose μ hfinite hg hlower hzero horizon hexcess hosc hB hfail using hbad
  let (j : ℕ) : IsFiniteMeasureOnCompacts (μ j) := hfinite j
  have hshift : Tendsto (fun j : ℕ => j + J₀) atTop atTop := tendsto_add_atTop_nat J₀
  obtain ⟨ρ, hρ, hlim⟩ := exists_original_excess_sequence_limit hnd μ C G hC hg hlower hzero
    (fun j => propagationScale (j + J₀)) (fun j => propagationHorizon (j + J₀))
    (propagationScale_tendsto_zero.comp hshift) (propagationHorizon_tendsto_atTop.comp hshift)
    (fun j => propagationScale_pos (j + J₀)) horizon b hb1 (by nlinarith)
    ((propagation_horizon_product_tendsto_zero b hb2).comp hshift) hexcess
    (fun j => propagationTestRadius (j + J₀)) (propagationTestRadius_tendsto_atTop.comp hshift)
    hosc D hB (propagation_last_error_tendsto_zero.comp hshift)
  obtain ⟨j, hj⟩ := ((hlim r hr).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).exists
  have hge : 1 ≤ squaredExcess (p + 1) (μ (ρ j)) 0 r / propagationScale (ρ j + J₀) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos (propagationScale_pos _))).mpr
    simpa only [one_mul] using! (hfail (ρ j)).le
  exact (not_lt_of_ge hge) hj

end

end RieszRectifiability

end OAI
