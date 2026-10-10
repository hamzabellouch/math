import Mathlib
import OAI.Analysis.FreeWords.MatrixAverageTrace
import OAI.Analysis.FreeWords.MatrixL2Definitions

namespace OAI

noncomputable section

namespace KKMatrixL2

open KKTraceTransfer KKUltraTrace KKProjectionSupport KKMatrixQuantization Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)

local instance matrixL2ClosurePartialOrder : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance matrixL2ClosurePreorder : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance matrixL2ClosureLE : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance matrixL2ClosureStarOrderedRing : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

lemma traceNorm_sum_le {J : Type*} (s : Finset J) (a : J → ConcreteAlgebra M) :
    traceNorm τ (∑ j∈s,a j) ≤ ∑ j∈s,traceNorm τ (a j) := by
  simp only [traceNorm_eq_gns,map_sum]
  exact norm_sum_le _ _

theorem matrix_l2_asymp_mul {I : Type*} {l : Filter I}
    (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M) (n : ℕ)
    (f f' g g' : I → MatrixAlg M n) (C D : ℝ)
    (hC : ∀ t i j, ‖f' t i j‖ ≤ C) (hD : ∀ t i j, ‖g t i j‖ ≤ D)
    (hf : ∀ i j, Tendsto (fun t => traceNorm τ (f t i j-f' t i j)) l (𝓝 0))
    (hg : ∀ i j, Tendsto (fun t => traceNorm τ (g t i j-g' t i j)) l (𝓝 0)) :
    ∀ i j, Tendsto (fun t => traceNorm τ ((f t*g t-f' t*g' t) i j)) l (𝓝 0) := by
  intro i j
  have hb (t:I) (k:Fin n) :
      traceNorm τ (f t i k*g t k j-f' t i k*g' t k j) ≤
        traceNorm τ (f t i k-f' t i k)*D+C*traceNorm τ (g t k j-g' t k j) := by
    have he : f t i k*g t k j-f' t i k*g' t k j =
        (f t i k-f' t i k)*g t k j+f' t i k*(g t k j-g' t k j) := by noncomm_ring
    rw [he]
    exact (traceNorm_add_le τ _ _).trans (add_le_add
      ((traceNorm_mul_right_le τ _ _).trans
        (mul_le_mul_of_nonneg_left (hD t k j) (traceNorm_nonneg τ _)))
      ((traceNorm_mul_le τ _ _).trans
        (mul_le_mul_of_nonneg_right (hC t i k) (traceNorm_nonneg τ _))))
  have ht (k:Fin n) : Tendsto
      (fun t => traceNorm τ (f t i k-f' t i k)*D+C*traceNorm τ (g t k j-g' t k j))
      l (𝓝 0) := by
    simpa only [zero_mul,mul_zero,zero_add] using ((hf i k).mul_const D).add ((hg k j).const_mul C)
  have hs : Tendsto (fun t => ∑ k:Fin n,
      (traceNorm τ (f t i k-f' t i k)*D+C*traceNorm τ (g t k j-g' t k j))) l (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun k _ => ht k)
  apply squeeze_zero (fun t => traceNorm_nonneg τ _) _ hs
  intro t
  change traceNorm τ ((f t*g t) i j-(f' t*g' t) i j) ≤ _
  simp only [Matrix.mul_apply,←Finset.sum_sub_distrib]
  exact (traceNorm_sum_le τ _ _).trans (Finset.sum_le_sum (fun k _ => hb t k))

end

end KKMatrixL2
end

end OAI
