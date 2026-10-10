import OAI.Analysis.LipschitzHilbert.Trees.UnaryPropagation

namespace OAI

/-! The segment log estimate with the starred amplitudes actually propagated. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

/-- Retain the exact total drop for the discarded-top contribution. -/
theorem unary_propagated_log_drop_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace ℂ E]
    (N : ℕ) (n : ℕ → ℝ) (A U W : ℕ → E) (beta : ℕ → ℝ) (coeff : ℕ → ℂ)
    {a p D ε : ℝ} (hp : 1 ≤ p) (ha : 1 ≤ a) (hap : a ≤ p)
    (hD : 0 ≤ D) (hε : 0 ≤ ε) (hstart : 4 ≤ n 0)
    (hn : ∀ i ≤ N, n 0 - 2 ≤ n i ∧ n i ≤ n 0)
    (hmass : ∀ i < N, n (i + 1) ≤ n i)
    (hcoeff : ∀ i < N, ‖coeff i‖ ≤ 1)
    (hstep : ∀ i < N, A i = coeff i • A (i + 1) + U i + W i)
    (hU : ∀ i ≤ N, ‖∑ j ∈ Finset.Ico i N, unaryPropagator coeff i j • U j‖ ≤ D)
    (hW : ∀ i < N, ‖W i‖ ≤ ε * (n i - n (i + 1)))
    (hbeta : ∀ i < N, 0 < beta i)
    (hprediction : ∀ i < N, beta i ≤ vertexAmount (n i) (A i) a p /
      (n i - n (i + 1) + vertexAmount (n (i + 1)) (A (i + 1)) a p)) :
    (∑ i ∈ Finset.range N, Real.log (beta i)) ≤
      4 * p * n 0 ^ ((a - 1) / p - 1) * (D + ε * (n 0 - n N)) := by
  let Astar := fun i => unaryPropagator coeff i N • A N
  have hdrop : 0 ≤ n 0 - n N := sub_nonneg.mpr (hn N le_rfl).2
  apply unary_vertex_telescope_short_segment N n A Astar beta hp ha hap
    (add_nonneg hD (mul_nonneg hε hdrop)) hstart
    (fun i hi => (hn i hi).1) hmass
  · intro i hi
    exact propagated_endpoint_contraction coeff (A N) hi (hcoeff i hi)
  · simp [Astar]
  · exact hbeta
  · exact hprediction
  · intro i hi
    have h := unary_perturbation_bound coeff A U W n hi
      (fun j hj => hcoeff j (Finset.mem_Ico.mp hj).2)
      (fun j hj => hstep j (Finset.mem_Ico.mp hj).2)
      (hU i hi) (fun j hj => hW j (Finset.mem_Ico.mp hj).2)
    exact h.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (sub_le_sub_right (hn i hi).2 _) hε))

theorem unary_propagated_log_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace ℂ E]
    (N : ℕ) (n : ℕ → ℝ) (A U W : ℕ → E) (beta : ℕ → ℝ) (coeff : ℕ → ℂ)
    {a p D ε : ℝ} (hp : 1 ≤ p) (ha : 1 ≤ a) (hap : a ≤ p)
    (hD : 0 ≤ D) (hε : 0 ≤ ε) (hstart : 4 ≤ n 0)
    (hn : ∀ i ≤ N, n 0 - 2 ≤ n i ∧ n i ≤ n 0)
    (hmass : ∀ i < N, n (i + 1) ≤ n i)
    (hcoeff : ∀ i < N, ‖coeff i‖ ≤ 1)
    (hstep : ∀ i < N, A i = coeff i • A (i + 1) + U i + W i)
    (hU : ∀ i ≤ N, ‖∑ j ∈ Finset.Ico i N, unaryPropagator coeff i j • U j‖ ≤ D)
    (hW : ∀ i < N, ‖W i‖ ≤ ε * (n i - n (i + 1)))
    (hbeta : ∀ i < N, 0 < beta i)
    (hprediction : ∀ i < N, beta i ≤ vertexAmount (n i) (A i) a p /
      (n i - n (i + 1) + vertexAmount (n (i + 1)) (A (i + 1)) a p)) :
    (∑ i ∈ Finset.range N, Real.log (beta i)) ≤
      4 * p * n 0 ^ ((a - 1) / p - 1) * (D + 2 * ε) := by
  let Astar := fun i => unaryPropagator coeff i N • A N
  apply unary_vertex_telescope_short_segment N n A Astar beta hp ha hap
    (by positivity) hstart (fun i hi => (hn i hi).1) hmass
  · intro i hi
    exact propagated_endpoint_contraction coeff (A N) hi (hcoeff i hi)
  · simp [Astar]
  · exact hbeta
  · exact hprediction
  · intro i hi
    have h := unary_perturbation_bound coeff A U W n hi
      (fun j hj => hcoeff j (Finset.mem_Ico.mp hj).2)
      (fun j hj => hstep j (Finset.mem_Ico.mp hj).2)
      (hU i hi) (fun j hj => hW j (Finset.mem_Ico.mp hj).2)
    change ‖A i - unaryPropagator coeff i N • A N‖ ≤ _
    have hdrop : n i - n N ≤ 2 := by linarith [(hn i hi).2, (hn N le_rfl).1]
    have htail : D + ε * (n i - n N) ≤ D + 2 * ε := by nlinarith
    exact h.trans htail

end LipschitzHilbert

end

end OAI
