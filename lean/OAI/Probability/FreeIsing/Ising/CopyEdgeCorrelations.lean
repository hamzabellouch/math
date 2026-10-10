import OAI.Probability.FreeIsing.Ising.CopyObservables

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor ColoredEdgeLifts

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def cavityLogEdgeVector
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (t : ℝ≥0) :
    EdgeSpace d (differenceSpace beta μ) :=
  WithLp.toLp 2 (fun c => observableDifference (beta := beta)
    (memLp_cavityLogObservable hμ hbeta t TreeEscape.root (prefixFlip c TreeEscape.root)))

theorem norm_cavityLogEdgeVector_sq_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (t : ℝ≥0)
    (o : TreeVertex d) :
    ‖cavityLogEdgeVector hμ hbeta t‖ ^ 2 ≤ (d : ℝ) *
      (cavityLogVarianceCoefficient (Real.tanh beta) *
        ∫ q, (IsingConditionalCopyBounds.fieldDifference beta o t q) ^ 2 ∂copies beta μ) := by
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ ≤ ∑ _c : Fin d, cavityLogVarianceCoefficient (Real.tanh beta) *
        ∫ q, (IsingConditionalCopyBounds.fieldDifference beta o t q) ^ 2 ∂copies beta μ := by
      apply Finset.sum_le_sum
      intro c hc
      exact norm_cavityLogDifference_sq_le hμ hbeta t o TreeEscape.root (prefixFlip c TreeEscape.root)
    _ = _ := by simp

theorem cavityLogEdgeVector_correlation_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t : ℝ≥0) (o : TreeVertex d) (n : ℕ),
      |inner ℝ (cavityLogEdgeVector hμ hbeta t)
        ((forwardOperator (by omega : 0 < d) (differenceReflection hμ)
          ((d : ℝ) - 1)⁻¹ ^ n) (cavityLogEdgeVector hμ hbeta t))| ≤
      (K * ((n : ℝ) + 1) * (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ n) *
        ((d : ℝ) * (cavityLogVarianceCoefficient (Real.tanh beta) *
          ∫ q, (IsingConditionalCopyBounds.fieldDifference beta o t q) ^ 2 ∂copies beta μ)) := by
  obtain ⟨K, hK, hpow⟩ := forwardOperator_pow_bound hμ hd hbeta hthreshold
  refine ⟨K, hK, ?_⟩
  intro t o n
  let f := cavityLogEdgeVector hμ hbeta t
  let N := forwardOperator (by omega : 0 < d) (differenceReflection hμ) ((d : ℝ) - 1)⁻¹
  have hinner : |inner ℝ f ((N ^ n) f)| ≤ ‖N ^ n‖ * ‖f‖ ^ 2 := by
    calc
      |inner ℝ f ((N ^ n) f)| ≤ ‖f‖ * ‖(N ^ n) f‖ :=
        by simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) f ((N ^ n) f)
      _ ≤ ‖f‖ * (‖N ^ n‖ * ‖f‖) :=
        mul_le_mul_of_nonneg_left ((N ^ n).le_opNorm f) (norm_nonneg f)
      _ = _ := by ring
  exact hinner.trans (mul_le_mul (hpow n)
    (norm_cavityLogEdgeVector_sq_le hμ hbeta t o) (sq_nonneg ‖f‖)
    (by positivity))

theorem summable_cavityLogEdgeVector_correlations
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) (t : ℝ≥0) :
    Summable (fun n : ℕ => |inner ℝ (cavityLogEdgeVector hμ hbeta t)
      ((forwardOperator (by omega : 0 < d) (differenceReflection hμ)
        ((d : ℝ) - 1)⁻¹ ^ n) (cavityLogEdgeVector hμ hbeta t))|) := by
  let f := cavityLogEdgeVector hμ hbeta t
  let N := forwardOperator (by omega : 0 < d) (differenceReflection hμ) ((d : ℝ) - 1)⁻¹
  apply Summable.of_nonneg_of_le (fun n => abs_nonneg _)
    (f := fun n => ‖N ^ n‖ * ‖f‖ ^ 2)
  · intro n
    calc
      |inner ℝ f ((N ^ n) f)| ≤ ‖f‖ * ‖(N ^ n) f‖ :=
        by simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) f ((N ^ n) f)
      _ ≤ ‖f‖ * (‖N ^ n‖ * ‖f‖) :=
        mul_le_mul_of_nonneg_left ((N ^ n).le_opNorm f) (norm_nonneg f)
      _ = _ := by ring
  · exact (summable_forwardOperator_pow hμ hd hbeta hthreshold).mul_right _

end Problem367.IsingCopySpectral

end

end OAI
