import Mathlib
import OAI.Analysis.WeakInfiniteness.ExactInfiniteness
import OAI.Analysis.WeakInfiniteness.MatrixTensorExact
import OAI.Analysis.WeakInfiniteness.NuclearApproximation

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra ComplexOrder

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem nuclear_exact (hA : Nuclear A) : Exact A := by
  intro C D _ _ q _ z hz
  let := CStarAlgebra.spectralOrder C
  let := CStarAlgebra.spectralOrderedRing C
  let := CStarAlgebra.spectralOrder D
  let := CStarAlgebra.spectralOrderedRing D
  have hzq : minimalMapRight q z=0 := (minimalMapRight_eq_zero_iff q z).mpr hz
  have hc : IsClosed (tensorKernelIdeal (A := A) q : Set (SpatialAmbient A C)) :=
    isClosed_closure
  change z.val ∈ (tensorKernelIdeal (A := A) q : Set (SpatialAmbient A C))
  rw [← hc.closure_eq]
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n,_,φ,ψ,hφ,hψ,_,_,he⟩ := nuclear_tensor_approximation hA z hε
  let y := minimalCPMap ψ (minimalCPMap φ z)
  have hφz : minimalMapRight q (minimalCPMap φ z)=0 := by
    rw [minimalCPMap_right_comm φ hφ,hzq,map_zero]
  have hym : y.val ∈ tensorKernelIdeal (A := A) q :=
    minimalCPMap_kernel ψ hψ q (minimalCPMap φ z) (matrixTensor_kernel q _ hφz)
  refine ⟨y.val,hym,?_⟩
  rw [dist_comm,dist_eq_norm]
  exact he

theorem nuclear_weaklyPurelyInfinite_stronglyPurelyInfinite
    (hA : Nuclear A) (hW : WeaklyPurelyInfinite A) : StronglyPurelyInfinite A :=
  exact_weaklyPurelyInfinite_stronglyPurelyInfinite A (nuclear_exact hA) hW

end

end WeakPureInfiniteness
end

end OAI
