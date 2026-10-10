import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.LinearAlgebra.DirectSum.Finsupp

namespace OAI

/-! # Tensoring group chains with a trivial coefficient module -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory MonoidalCategory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2

variable {k G : Type} [CommRing k] [Group G] (V : ModuleCat k) (A : Rep k G)

def trivialTensorCoefficient : Rep k G := Rep.trivial k G V ⊗ A

theorem trivialTensorCoefficient_tmul (g : G) (v : V) (a : A) :
    (trivialTensorCoefficient V A).ρ g (v ⊗ₜ[k] a) = v ⊗ₜ[k] A.ρ g a := by
  change TensorProduct.map (LinearMap.id : V →ₗ[k] V) (A.ρ g) (v ⊗ₜ[k] a) = _
  rw [TensorProduct.map_tmul, LinearMap.id_apply]

def trivialTensorChainsIso [DecidableEq G] :
    ((tensorLeft V).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (groupHomology.inhomogeneousChains A) ≅
      groupHomology.inhomogeneousChains (trivialTensorCoefficient V A) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => (TensorProduct.finsuppRight k k V A.V (Fin i → G)).toModuleIso) ?_
  rintro i j rfl
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro v
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext
  intro a
  change (groupHomology.inhomogeneousChains (trivialTensorCoefficient V A)).d (j + 1) j
      (TensorProduct.finsuppRight k k V A.V (Fin (j + 1) → G)
        (v ⊗ₜ[k] Finsupp.single x a)) =
    TensorProduct.finsuppRight k k V A.V (Fin j → G)
      (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
        ((groupHomology.inhomogeneousChains A).d (j + 1) j).hom
        (v ⊗ₜ[k] Finsupp.single x a))
  rw [groupHomology.inhomogeneousChains.d_def, groupHomology.inhomogeneousChains.d_def,
    TensorProduct.finsuppRight_tmul_single, TensorProduct.map_tmul, LinearMap.id_apply]
  erw [groupHomology.inhomogeneousChains.d_single,
    groupHomology.inhomogeneousChains.d_single, trivialTensorCoefficient_tmul]
  simp only [TensorProduct.tmul_add, TensorProduct.tmul_sum, map_add, map_sum,
    TensorProduct.finsuppRight_tmul_single]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [TensorProduct.tmul_smul, map_smul, TensorProduct.finsuppRight_tmul_single]
  rfl

end PolycyclicRecognition

end

end OAI
