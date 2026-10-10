import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Absorption.CentralHalfFlipIntertwining
import OAI.Analysis.JiangSu.Absorption.TensorIdealAbsorption
import OAI.Analysis.JiangSu.TensorProducts.HilbertTensorCache

namespace OAI


noncomputable section
namespace ActualSpatial
open Pureness CStarAbsorption Filter
open scoped CStarAlgebra TensorProduct

universe u v
variable (A : Type u) (D : Type v) [CStarAlgebra A] [CStarAlgebra D]
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D]

lemma rightHom_injective [Nontrivial A] : Function.Injective (rightHom A D) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro d hd
  have he : tensorMap A D ((1 : A) ⊗ₜ[ℂ] d)=tensorMap A D 0 := by
    simpa only [tensorMap_tmul,map_one,one_mul,map_zero] using hd
  have hz := tensorMap_injective A D he
  simpa only [Module.FaithfullyFlat.one_tmul_eq_zero_iff] using hz

variable [Nontrivial A] [Nontrivial D]
variable [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace D]
variable (U : Ultrafilter ℕ)
variable (φ : D →⋆ₐ[ℂ] NormUltra.QuotientAlgebra (fun _ : ℕ=>A) U)
variable (hφ : ∀ a d,Commute (NormUltra.QuotientAlgebra.diagonalHom U a) (φ d))
variable (hD : IsNuclear.{v,v} D) (hs : Pureness.TopologicallySimple D)
variable (hh : ApproximateInnerHalfFlip (tensorMap D D))
include U φ hφ hD hs hh in
 theorem unital_absorption_of_embedding : Nonempty (A ≃⋆ₐ[ℂ] Tensor A D) := by
  have he : commutingStarTensorHom (leftHom A D) (rightHom A D) (homs_commute A D)=tensorMap A D := by
    apply StarAlgHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a d => rfl
    | add x y hx hy => simp only [map_add,hx,hy]
  apply equiv_of_nuclear_half_flip hD hs (tensorMap D D) (tensorMap_injective D D)
    (tensorMap_dense D D) hh U (leftHom A D) (rightHom A D) (homs_commute A D)
    (rightHom_injective A D) φ hφ
  · exact NonUnitalStarAlgHom.isometry (leftHom A D) (leftHom_injective A D)
  · exact (congrArg (fun hom : A ⊗[ℂ] D →⋆ₐ[ℂ] Tensor A D => DenseRange hom) he).mpr
      (tensorMap_dense A D)

end ActualSpatial

end


noncomputable section
namespace ActualSpatial
open Pureness NonunitalRelative CStarAbsorption NonunitalTensor NonunitalGamma Filter
open scoped CStarAlgebra TensorProduct

universe u
variable (A : Type*) (D : Type u) [NonUnitalCStarAlgebra A] [CStarAlgebra D]
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D]

variable [Nontrivial A] [Nontrivial D]
variable [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace D]
variable (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ)≤atTop)]
variable (φ : D →⋆ₐ[ℂ] CentralSequenceAlgebra (A := A) U)
variable (hD : IsNuclear.{u,u} D) (hs : Pureness.TopologicallySimple D)
variable (hh : ConnectedApproximateInnerHalfFlip (tensorMap D D))
include U φ hD hs hh in

theorem nonunital_absorption_of_embedding : Nonempty (A ≃⋆ₐ[ℂ] NonunitalTensor A D) := by
  exact NonunitalTensor.equiv_of_embedding
    (leftHom (Unitization ℂ A) D) (rightHom (Unitization ℂ A) D)
    (homs_commute (Unitization ℂ A) D) U φ hD hs (tensorMap D D)
    (tensorMap_injective D D) (tensorMap_dense D D) hh
    (leftHom_injective (Unitization ℂ A) D)
    (tensorMap (Unitization ℂ A) D) (tensorMap_dense (Unitization ℂ A) D)
    (tensorMap_tmul (Unitization ℂ A) D)

end ActualSpatial

end

end OAI
