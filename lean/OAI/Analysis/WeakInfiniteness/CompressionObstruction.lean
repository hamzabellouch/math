import Mathlib
import OAI.Analysis.WeakInfiniteness.ElementaryCP

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

local instance compressionObstructionPartialOrder : PartialOrder OInfinity :=
  CStarAlgebra.spectralOrder _

local instance compressionObstructionStarOrderedRing : StarOrderedRing OInfinity :=
  CStarAlgebra.spectralOrderedRing _

lemma exists_unital_cpc_compression_killing_isometry :
    ∃ Φ : OInfinity →L[ℂ] OInfinity,CompletelyPositive Φ ∧ ‖Φ‖≤1 ∧
      Φ 1=1 ∧
      star (oInfinityIsometry 1)*oInfinityIsometry 1=1 ∧
      Φ (oInfinityIsometry 1)=0 ∧
      Φ (star (oInfinityIsometry 1)*oInfinityIsometry 1)≠
        star (Φ (oInfinityIsometry 1))*Φ (oInfinityIsometry 1) := by
  let v : Fin 1 → OInfinity := fun _ => oInfinityIsometry 0
  have h00 : star (oInfinityIsometry 0)*oInfinityIsometry 0=1 := (oInfinityIsometry_relations 0 0).trans (ite_eq_left rfl)
  have h01 : star (oInfinityIsometry 0)*oInfinityIsometry 1=0 := (oInfinityIsometry_relations 0 1).trans (ite_eq_right (by decide))
  have h11 : star (oInfinityIsometry 1)*oInfinityIsometry 1=1 := (oInfinityIsometry_relations 1 1).trans (ite_eq_left rfl)
  have he (a : OInfinity) : finiteCompressionContinuous v a=
      star (oInfinityIsometry 0)*a*oInfinityIsometry 0 := by
    simp only [finiteCompressionContinuous_apply,finiteCompression,Fin.sum_univ_one,v]
  have hn : ‖finiteCompressionContinuous v‖≤1 := by
    have h := finiteCompressionContinuous_norm_le v
    simpa only [Fin.sum_univ_one,v,h00,norm_one] using h
  have hu : finiteCompressionContinuous v 1=1 := by rw [he,mul_one,h00]
  have hz : finiteCompressionContinuous v (oInfinityIsometry 1)=0 := by
    rw [he,h01,zero_mul]
  refine ⟨finiteCompressionContinuous v,finiteCompressionContinuous_cp v,hn,hu,h11,hz,?_⟩
  rw [h11,hu,hz,star_zero,zero_mul]
  intro h
  have hn := congrArg norm h
  norm_num only [norm_one,norm_zero] at hn

end

end WeakPureInfiniteness
end

end OAI
