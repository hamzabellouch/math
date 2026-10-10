import OAI.Probability.FreeIsing.Ising.CopyGeodesicCorrelations
import OAI.Probability.FreeIsing.Trees.RootedTransitivity

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor ColoredEdgeLifts

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem norm_cavityLogVector_sq_eq
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v w : TreeVertex d) :
    ‖cavityLogVector hμ hbeta t v w‖ ^ 2 =
      ∫ q, (cavityLogDifference hbeta t v w q) ^ 2 ∂copies beta μ := by
  rw [← real_inner_self_eq_norm_sq, inner_cavityLogVector_eq_integral]
  simp only [pow_two]

theorem norm_cavityLogVector_sq_eq_of_adj
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {u v x y : TreeVertex d} (huv : treeAdj u v) (hxy : treeAdj x y) :
    ‖cavityLogVector hμ hbeta t u v‖ ^ 2 =
      ‖cavityLogVector hμ hbeta t x y‖ ^ 2 := by
  obtain ⟨g, hgu, hgv⟩ := exists_treeAut_map_adjacent_pair huv hxy
  have h := inner_cavityLogVector_map hμ hbeta g t u v u v
  rw [hgu, hgv] at h
  simpa only [real_inner_self_eq_norm_sq] using h.symm

theorem integral_cavityLogDifference_sq_eq_of_adj
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {u v x y : TreeVertex d} (huv : treeAdj u v) (hxy : treeAdj x y) :
    (∫ q, (cavityLogDifference hbeta t u v q) ^ 2 ∂copies beta μ) =
      ∫ q, (cavityLogDifference hbeta t x y q) ^ 2 ∂copies beta μ := by
  rw [← norm_cavityLogVector_sq_eq hμ hbeta t u v,
    ← norm_cavityLogVector_sq_eq hμ hbeta t x y]
  exact norm_cavityLogVector_sq_eq_of_adj hμ hbeta t huv hxy

theorem norm_cavityLogEdgeVector_sq_eq
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {u v : TreeVertex d} (huv : treeAdj u v) :
    ‖cavityLogEdgeVector hμ hbeta t‖ ^ 2 = (d : ℝ) *
      ∫ q, (cavityLogDifference hbeta t u v q) ^ 2 ∂copies beta μ := by
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ = ∑ _c : Fin d, ‖cavityLogVector hμ hbeta t u v‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro c hc
      change ‖cavityLogVector hμ hbeta t TreeEscape.root
        (prefixFlip c TreeEscape.root)‖ ^ 2 = _
      exact norm_cavityLogVector_sq_eq_of_adj hμ hbeta t (Or.inl ⟨c, rfl⟩) huv
    _ = (d : ℝ) * ‖cavityLogVector hμ hbeta t u v‖ ^ 2 := by simp
    _ = _ := by rw [norm_cavityLogVector_sq_eq]

end Problem367.IsingCopySpectral

end

end OAI
