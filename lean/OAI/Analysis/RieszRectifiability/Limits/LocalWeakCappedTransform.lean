import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactLimitCappedTransform
import OAI.Analysis.RieszRectifiability.Limits.WeakL2Subsequence

namespace OAI

/-!
# Local weak limits of capped transforms

Uniform L² bounds yield weakly convergent subsequences of scalar capped transforms
at dyadic truncation scales, both for finite measures and for finite ball restrictions.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

theorem exists_scalarCappedTransform_weak_subsequence {d : ℕ} (m : ℕ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (e : Ambient d) (A : ℝ≥0)
    (hB : ∀ ε : ℝ, 0 < ε →
      MemLp (scalarCappedTransform m ν e ε (fun _ => 1)) 2 ν ∧
        eLpNorm (scalarCappedTransform m ν e ε (fun _ => 1)) 2 ν ≤
          (A : ℝ≥0∞) * eLpNorm (fun _ : Ambient d => (1 : ℝ)) 2 ν) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      Tendsto (fun j => (1 / 2 : ℝ) ^ (ρ j)) atTop (𝓝 0) ∧
      ∃ v : Lp ℝ 2 ν, ‖v‖ ≤ (A : ℝ) * Real.sqrt (ν.real univ) ∧
        ∀ g : Ambient d → ℝ, MemLp g 2 ν →
          Tendsto (fun j => ∫ x, scalarCappedTransform m ν e ((1 / 2 : ℝ) ^ (ρ j))
            (fun _ => 1) x * g x ∂ν) atTop (𝓝 (∫ x, v x * g x ∂ν)) := by
  let F := fun j : ℕ => scalarCappedTransform m ν e ((1 / 2 : ℝ) ^ j) (fun _ => 1)
  have hF : ∀ j, MemLp (F j) 2 ν := fun j => (hB _ (by positivity)).1
  have hconst : MemLp (fun _ : Ambient d => (1 : ℝ)) 2 ν := memLp_const 1
  have hc := toLp_norm_eq_sqrt_integral ν (fun _ : Ambient d => (1 : ℝ)) hconst
  simp only [Lp.norm_toLp, one_pow, integral_const, smul_eq_mul, mul_one] at hc
  have hnorm (j : ℕ) : ‖(hF j).toLp (F j)‖ ≤ (A : ℝ) * Real.sqrt (ν.real univ) := by
    have hfin : (A : ℝ≥0∞) * eLpNorm (fun _ : Ambient d => (1 : ℝ)) 2 ν ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top hconst.eLpNorm_ne_top
    have h := ENNReal.toReal_mono hfin (hB ((1 / 2 : ℝ) ^ j) (by positivity)).2
    simpa only [Lp.norm_toLp, ENNReal.toReal_mul, ENNReal.coe_toReal, hc] using! h
  obtain ⟨ρ, hρ, v, hv, hlim⟩ := bounded_L2_sequence_weak_subsequence ν F hF
    ((A : ℝ) * Real.sqrt (ν.real univ)) hnorm
  refine ⟨ρ, hρ, ?_, v, hv, hlim⟩
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).comp hρ.tendsto_atTop

theorem exists_local_weak_transform_of_source_L2 {d : ℕ} (m : ℕ) (hm : 1 ≤ m) (C : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hgrowth : ∀ j, GlobalUpperGrowth m C (μ j)) (hweak : CompactTestConvergence μ ν)
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 (μ j) →
      MemLp (truncated m (μ j) ε f) 2 (μ j) ∧
        eLpNorm (truncated m (μ j) ε f) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm f 2 (μ j))
    (a : Ambient d) (R : ℝ)
    (hboundary : ν (frontier (ball a R)) = 0) (hmass : ν (ball a R) ≠ 0) (e : Ambient d) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      Tendsto (fun j => (1 / 2 : ℝ) ^ (ρ j)) atTop (𝓝 0) ∧
      ∃ v : Lp ℝ 2 (ν.restrict (ball a R)),
        ‖v‖ ≤ (Real.toNNReal (‖e‖ * ((D : ℝ) + C * 2 ^ m)) : ℝ) *
          Real.sqrt (ν.real (ball a R)) ∧
        ∀ g : Ambient d → ℝ, MemLp g 2 (ν.restrict (ball a R)) →
          Tendsto (fun j => ∫ x in ball a R,
            scalarCappedTransform m (ν.restrict (ball a R)) e ((1 / 2 : ℝ) ^ (ρ j))
              (fun _ => 1) x * g x ∂ν) atTop (𝓝 (∫ x in ball a R, v x * g x ∂ν)) := by
  have hcompact : IsCompact (closure (ball a R)) :=
    (isCompact_closedBall a R).of_isClosed_subset isClosed_closure
      (closure_minimal ball_subset_closedBall isClosed_closedBall)
  let := relativelyCompact_restrict_finite ν (ball a R) hcompact
  have h := exists_scalarCappedTransform_weak_subsequence m (ν.restrict (ball a R)) e
    (Real.toNNReal (‖e‖ * ((D : ℝ) + C * 2 ^ m))) (fun ε hε =>
      compact_limit_scalarCappedTransform_L2_bound m hm C μ ν hgrowth hweak D hB
        a R hboundary hmass e ε hε (BoundedContinuousFunction.const (Ambient d) 1))
  simpa only [Measure.real, Measure.restrict_apply_univ] using! h

end

end RieszRectifiability

end OAI
