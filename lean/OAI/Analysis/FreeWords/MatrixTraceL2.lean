import Mathlib
import OAI.Analysis.FreeWords.MatrixL2Definitions
import OAI.Analysis.FreeWords.ProjectionRound

namespace OAI

noncomputable section

namespace KKMatrixL2

open KKTraceTransfer Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {I : Type*} {M : VonNeumannAlgebra H} {n : ℕ}

open KKUltraTrace KKProjectionSupport

open scoped InnerProductSpace

local instance : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

lemma norm_trace_le_traceNorm (τ : FaithfulNormalTrace M) (x : ConcreteAlgebra M) :
    ‖τ.map x‖ ≤ traceNorm τ x := by
  have hh := norm_inner_le_norm (𝕜 := ℂ) (gnsVector (tracePositive τ) (1:ConcreteAlgebra M))
    (gnsVector (tracePositive τ) x)
  simp only [gnsVector_inner,star_one,one_mul,←traceNorm_eq_gns,traceNorm_one,one_mul] at hh
  change ‖τ.map x‖ ≤ traceNorm τ x at hh
  exact hh

theorem matrix_trace_l2_null {l : Filter I} (τ : FaithfulNormalTrace M)
    (f : I → MatrixAlg M n)
    (hf : ∀ i j, Tendsto (fun t => traceNorm τ (f t i j)) l (𝓝 0)) :
    Tendsto (fun t => (n:ℂ)⁻¹ * ∑ i,τ.map (f t i i)) l (𝓝 0) := by
  have ht (i:Fin n) : Tendsto (fun t => τ.map (f t i i)) l (𝓝 0) :=
    squeeze_zero_norm (fun t => norm_trace_le_traceNorm τ _) (hf i i)
  have hs := tendsto_finsetSum Finset.univ (fun i _ => ht i)
  simpa only [Finset.sum_const_zero,mul_zero] using hs.const_mul (n:ℂ)⁻¹

end

end KKMatrixL2
end

end OAI
