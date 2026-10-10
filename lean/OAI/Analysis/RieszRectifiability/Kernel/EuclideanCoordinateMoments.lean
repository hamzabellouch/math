import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

/-!
# Euclidean second moments from coordinate moments

The squared Euclidean norm is a finite sum of squared coordinates. This identity
transfers coordinatewise integrability, integral formulas, and convergence of
second moments to their Euclidean counterparts, including varying measures.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology

theorem integrable_euclidean_norm_sq_of_coordinates {X : Type*} [MeasurableSpace X] {q : ℕ}
    (μ : Measure X) (w : X → Ambient q)
    (hi : ∀ i : Fin q, Integrable (fun x => (w x i) ^ 2) μ) :
    Integrable (fun x => ‖w x‖ ^ 2) μ := by
  simpa only [EuclideanSpace.real_norm_sq_eq] using!
    integrable_finsetSum Finset.univ (fun i _ => hi i)

theorem integral_euclidean_norm_sq_eq_sum {X : Type*} [MeasurableSpace X] {q : ℕ}
    (μ : Measure X) (w : X → Ambient q)
    (hi : ∀ i : Fin q, Integrable (fun x => (w x i) ^ 2) μ) :
    (∫ x, ‖w x‖ ^ 2 ∂μ) = ∑ i : Fin q, ∫ x, (w x i) ^ 2 ∂μ := by
  simp only [EuclideanSpace.real_norm_sq_eq]
  exact integral_finsetSum Finset.univ (fun i _ => hi i)

theorem euclidean_norm_sq_tendsto_zero_of_coordinates
    {X : Type*} [MeasurableSpace X] {q : ℕ}
    (μ : ℕ → Measure X) (w : ℕ → X → Ambient q)
    (hi : ∀ j i, Integrable (fun x => (w j x i) ^ 2) (μ j))
    (hlim : ∀ i : Fin q,
      Tendsto (fun j => ∫ x, (w j x i) ^ 2 ∂μ j) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, ‖w j x‖ ^ 2 ∂μ j) atTop (𝓝 0) := by
  simp_rw [integral_euclidean_norm_sq_eq_sum _ _ (hi _)]
  simpa only [Finset.sum_const_zero] using!
    tendsto_finsetSum Finset.univ (fun i _ => hlim i)

end

end RieszRectifiability

end OAI
