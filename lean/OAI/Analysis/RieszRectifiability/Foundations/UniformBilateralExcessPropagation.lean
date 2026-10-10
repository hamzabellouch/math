import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.UniformExcessPropagation
import OAI.Analysis.RieszRectifiability.Limits.OriginalBilateralSequenceLimit

namespace OAI

/-!
# Uniform bilateral excess propagation

The conclusion combines a squared-excess estimate with bilateral beta smallness.
A contradiction sequence first yields bilateral convergence and then a further
subsequence with vanishing normalized excess, producing one propagation index
that works uniformly for all measures satisfying the stated bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

def ExcessBilateralConclusion {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (r δ ε : ℝ) : Prop :=
  squaredExcess n μ 0 r ≤ δ ^ 2 ∧ bilateralBeta n μ 0 r < ε

theorem exists_uniform_bilateral_excess_propagation {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (hC : 0 < C) (b : ℝ) (hb1 : 1 < b) (hb2 : b ^ 2 < 2)
    (D : ℝ≥0) (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) (J₀ : ℕ) :
    ∃ J : ℕ, J₀ ≤ J ∧ ∀ μ : Measure (Ambient d),
      IsFiniteMeasureOnCompacts μ → GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ s : ℝ, AdmissibleRadius μ s →
        ENNReal.ofReal (s ^ (p + 1) / C) ≤ μ (ball x s)) →
      (0 : Ambient d) ∈ μ.support →
      AdmissibleRadius μ ((2 : ℝ) ^ propagationHorizon J) →
      (∀ l ≤ propagationHorizon J,
        squaredExcess (p + 1) μ 0 ((2 : ℝ) ^ l) ≤ (propagationScale J * b ^ l) ^ 2) →
      ScalarOscillationBound (p + 1) μ 0 (propagationTestRadius J) (propagationScale J ^ 3) →
      (∀ η, 0 < η → ∀ u : Ambient d → ℝ, MemLp u 2 μ →
        MemLp (truncated (p + 1) μ η u) 2 μ ∧
          eLpNorm (truncated (p + 1) μ η u) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm u 2 μ) →
      ExcessBilateralConclusion (p + 1) μ r (propagationScale J) ε := by
  classical
  by_contra h
  push Not at h
  have hbad (j : ℕ) := h (j + J₀) (by omega)
  choose μ hfinite hg hlower hzero horizon hexcess hosc hB hfail using hbad
  let (j : ℕ) : IsFiniteMeasureOnCompacts (μ j) := hfinite j
  have hshift : Tendsto (fun j : ℕ => j + J₀) atTop atTop := tendsto_add_atTop_nat J₀
  obtain ⟨ρ, hρ, hbilateral⟩ := exists_original_bilateral_sequence_limit hnd μ C G hC hg hlower hzero
    (fun j => propagationScale (j + J₀)) (fun j => propagationHorizon (j + J₀))
    (propagationScale_tendsto_zero.comp hshift) (propagationHorizon_tendsto_atTop.comp hshift)
    (fun j => propagationScale_pos (j + J₀)) horizon b hb1
    ((propagation_horizon_product_tendsto_zero b hb2).comp hshift) hexcess
    (fun j => propagationTestRadius (j + J₀)) (propagationTestRadius_tendsto_atTop.comp hshift) hosc
  have hindices : Tendsto (fun j => ρ j + J₀) atTop atTop := hshift.comp hρ.tendsto_atTop
  obtain ⟨τ, hτ, hlim⟩ := exists_original_excess_sequence_limit hnd (fun j => μ (ρ j)) C G hC
    (fun j => hg (ρ j)) (fun j => hlower (ρ j)) (fun j => hzero (ρ j))
    (fun j => propagationScale (ρ j + J₀)) (fun j => propagationHorizon (ρ j + J₀))
    (propagationScale_tendsto_zero.comp hindices) (propagationHorizon_tendsto_atTop.comp hindices)
    (fun j => propagationScale_pos (ρ j + J₀)) (fun j => horizon (ρ j)) b hb1 (by nlinarith)
    ((propagation_horizon_product_tendsto_zero b hb2).comp hindices) (fun j => hexcess (ρ j))
    (fun j => propagationTestRadius (ρ j + J₀)) (propagationTestRadius_tendsto_atTop.comp hindices)
    (fun j => hosc (ρ j)) D (fun j => hB (ρ j))
    (propagation_last_error_tendsto_zero.comp hindices)
  have he := (hlim r hr.le).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hb := ((hbilateral r hr).comp hτ.tendsto_atTop).eventually (gt_mem_nhds hε)
  obtain ⟨j, hj, hjb⟩ := (he.and hb).exists
  apply hfail (ρ (τ j))
  refine ⟨?_, hjb⟩
  have heq := (div_lt_iff₀ (sq_pos_of_pos (propagationScale_pos (ρ (τ j) + J₀)))).mp hj
  simpa only [one_mul] using! heq.le

end

end RieszRectifiability

end OAI
