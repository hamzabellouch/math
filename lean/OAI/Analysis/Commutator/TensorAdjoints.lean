import Mathlib
import OAI.Analysis.Commutator.TensorMultiplicity2

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.HilbertTensor

open ContinuousLinearMap

variable {E F J K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

lemma scalarSlice_adjoint
    (T : Completion (E ⊗[ℂ] J) →L[ℂ] Completion (F ⊗[ℂ] K))
    (a : K) (b : J) : scalarSlice T.adjoint a b = (scalarSlice T b a).adjoint := by
  simp only [scalarSlice, adjoint_comp, adjoint_adjoint, ContinuousLinearMap.comp_assoc]

omit [CompleteSpace E] in
lemma multiplicityCompression_adjoint [CompleteSpace J]
    (T : Completion (E ⊗[ℂ] J) →L[ℂ] Completion (E ⊗[ℂ] J)) (v : E) :
    multiplicityCompression T.adjoint v = (multiplicityCompression T v).adjoint := by
  simp only [multiplicityCompression, adjoint_comp, adjoint_adjoint, ContinuousLinearMap.comp_assoc]

lemma isometry_adjoint_fix (U : E →ₗᵢ[ℂ] E) (v : E) (h : U v = v) :
    U.toContinuousLinearMap.adjoint v = v := by
  conv_lhs => rw [← h]
  exact congrArg (fun T : E →L[ℂ] E => T v) U.adjoint_comp_self

lemma repeated_pair_adjoint [CompleteSpace J] {ι : Type*} [Fintype ι]
    (T : Completion (E ⊗[ℂ] J) →L[ℂ] Completion (E ⊗[ℂ] J))
    (U : ι → E →ₗᵢ[ℂ] E)
    (hclass : ∀ a b : J, ∃ c : ι → ℂ,
      scalarSlice T a b = ∑ i, c i • (U i).toContinuousLinearMap)
    (v w : E) (hv : ‖v‖ = 1) (hUv : ∀ i, U i v = v) (hUw : ∀ i, U i w = w)
    (a : J) : T.adjoint (pair w a) = pair w ((multiplicityCompression T v).adjoint a) := by
  rw [← multiplicityCompression_adjoint]
  have hclassAdj : ∀ b c : J, ∃ d : ι → ℂ,
      scalarSlice T.adjoint b c = ∑ i, d i • (U i).toContinuousLinearMap.adjoint := by
    intro b c
    obtain ⟨d, hd⟩ := hclass c b
    refine ⟨fun i => star (d i), ?_⟩
    rw [scalarSlice_adjoint, hd]
    simp only [map_sum, map_smulₛₗ, starRingEnd_apply]
  exact repeated_pair T.adjoint (fun i => (U i).toContinuousLinearMap.adjoint) hclassAdj v w hv
    (fun i => isometry_adjoint_fix (U i) v (hUv i))
    (fun i => isometry_adjoint_fix (U i) w (hUw i)) a

end Kadison.HilbertTensor
end

end OAI
