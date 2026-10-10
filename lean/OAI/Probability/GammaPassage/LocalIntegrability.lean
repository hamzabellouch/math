import OAI.Probability.GammaPassage.FiniteSumIntegrability
import OAI.Probability.GammaPassage.LocalRegularity

namespace OAI

namespace GammaFPP.FiniteLocal
open MeasureTheory ProbabilityTheory PlanarFPP

/-- Nonnegative candidate cost is bounded by the sum on its containing edge set.
Nodup is essential: the finite coordinates are physical edges, not traversals. -/
lemma finitePassageTime_le_sum (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) (v : Coordinates p q R)
    (hv : ∀ e, 0 ≤ v e) : finitePassageTime p q R v ≤ ∑ e, v e := by
  classical
  obtain ⟨ds, hds⟩ := candidates_nonempty p q R hR
  have hn := ((mem_candidates p q R ds).mp hds).2.1
  have hsub := candidate_edges_subset p q R ds hds
  have hw := extend_nonneg p q R v hv
  change passageTime (extend p q R v) p q R ≤ _
  apply (passageTime_le_candidate (extend p q R v) p q R ds hds).trans
  rw [pathCost_eq_distinct_edgeSum (extend p q R v) p ds hn]
  calc
    _ ≤ ∑ e ∈ localEdges p q R, extend p q R v e :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => hw e)
    _ = ∑ e : ↥(localEdges p q R), v e := by
      rw [← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro e _
      exact extend_apply p q R v e

lemma finitePassageTime_nonneg (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) (v : Coordinates p q R)
    (hv : ∀ e, 0 ≤ v e) : 0 ≤ finitePassageTime p q R v :=
  passageTime_nonneg (extend p q R v) (extend_nonneg p q R v hv) p q R hR

/-- All real t<=rate/2 are allowed, including arbitrarily negative t. -/
theorem integrable_finitePassageTime_exp {shape rate : ℝ}
    (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R)
    (t : ℝ) (ht : t ≤ rate/2) :
    Integrable (fun v => Real.exp (t * finitePassageTime p q R v))
      (finiteGammaMeasure (ι := ↥(localEdges p q R)) shape rate) := by
  have hi := finite_gamma_integrable_exp_sum (ι := ↥(localEdges p q R)) hs hr
    (show rate/2 < rate by linarith)
  have hm : Measurable (fun v => Real.exp (t * finitePassageTime p q R v)) :=
    Real.measurable_exp.comp (measurable_const.mul (measurable_finitePassageTime p q R hR))
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [finiteGammaMeasure_ae_nonneg (ι := ↥(localEdges p q R)) hs hr] with v hv
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact (mul_le_mul_of_nonneg_right ht (finitePassageTime_nonneg p q R hR v hv)).trans
    (mul_le_mul_of_nonneg_left (finitePassageTime_le_sum p q R hR v hv) (by positivity))

end GammaFPP.FiniteLocal

end OAI
