import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalRepresentationFunctor
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalHomologyDimension

namespace OAI

/-! # Scalar extension of the actual inhomogeneous bar complex -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2300] TensorProduct.instModule Finsupp.module
variable {G : Type} [Group G]

def rationalizeGroupChainsIso (A : Rep.{0} ℤ G) :
    ((rationalModuleFunctor.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (groupHomology.inhomogeneousChains A)) ≅
        groupHomology.inhomogeneousChains (rationalizeRepresentation A) := by
  classical
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => (TensorProduct.finsuppRight ℤ ℚ ℚ A.V (Fin i → G)).toModuleIso) ?_
  rintro i j rfl
  apply ModuleCat.hom_ext
  let L : (ℚ ⊗[ℤ] ((Fin (j + 1) → G) →₀ A.V)) →ₗ[ℚ]
      ((Fin j → G) →₀ (ℚ ⊗[ℤ] A.V)) :=
    ((TensorProduct.finsuppRight ℤ ℚ ℚ A.V (Fin (j + 1) → G)).toModuleIso.hom ≫
      (groupHomology.inhomogeneousChains (rationalizeRepresentation A)).d (j + 1) j).hom
  let R : (ℚ ⊗[ℤ] ((Fin (j + 1) → G) →₀ A.V)) →ₗ[ℚ]
      ((Fin j → G) →₀ (ℚ ⊗[ℤ] A.V)) :=
    ((((rationalModuleFunctor.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (groupHomology.inhomogeneousChains A)).d (j + 1) j) ≫
      (TensorProduct.finsuppRight ℤ ℚ ℚ A.V (Fin j → G)).toModuleIso.hom).hom
  change L = R
  apply TensorProduct.AlgebraTensorModule.ext
  intro q f
  induction f using Finsupp.induction_linear with
  | zero => simp only [TensorProduct.tmul_zero, map_zero]
  | add f h hf hh => simp only [TensorProduct.tmul_add, map_add, hf, hh]
  | single x a =>
    change (groupHomology.inhomogeneousChains (rationalizeRepresentation A)).d (j + 1) j
      (TensorProduct.finsuppRight ℤ ℚ ℚ A.V (Fin (j + 1) → G)
        (q ⊗ₜ[ℤ] Finsupp.single x a)) =
      TensorProduct.finsuppRight ℤ ℚ ℚ A.V (Fin j → G)
        (((groupHomology.inhomogeneousChains A).d (j + 1) j).hom.baseChange ℚ
          (q ⊗ₜ[ℤ] Finsupp.single x a))
    rw [groupHomology.inhomogeneousChains.d_def, groupHomology.inhomogeneousChains.d_def,
      TensorProduct.finsuppRight_tmul_single]
    change groupHomology.inhomogeneousChains.d (rationalizeRepresentation A) j
      (Finsupp.single x (q ⊗ₜ[ℤ] a)) =
      TensorProduct.finsuppRight ℤ ℚ ℚ A.V (Fin j → G)
        (q ⊗ₜ[ℤ] groupHomology.inhomogeneousChains.d A j (Finsupp.single x a))
    let qa : rationalizeRepresentation A := q ⊗ₜ[ℤ] a
    change groupHomology.inhomogeneousChains.d (rationalizeRepresentation A) j
      (Finsupp.single x qa) = _
    rw [groupHomology.inhomogeneousChains.d_single]
    change _ = TensorProduct.finsuppRight ℤ ℚ ℚ A.V (Fin j → G)
      (q ⊗ₜ[ℤ] groupHomology.inhomogeneousChains.d A j (Finsupp.single x a))
    rw [groupHomology.inhomogeneousChains.d_single]
    simp only [TensorProduct.tmul_add, TensorProduct.tmul_sum, map_add, map_sum,
      TensorProduct.finsuppRight_tmul_single]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    dsimp only [qa, rationalizeRepresentation, Rep.of]
    change ((-1 : ℚ) ^ (l.val + 1)) •
        (Finsupp.single (l.contractNth (· * ·) x) (q ⊗ₜ[ℤ] a) :
          (Fin j → G) →₀ (ℚ ⊗[ℤ] A.V)) = _
    simp only [Finsupp.smul_single, TensorProduct.finsuppRight_tmul_single]
    rcases Nat.even_or_odd (l.val + 1) with h | h
    · simp only [h.neg_one_pow, one_smul]
      congr 2
      exact (@one_smul ℤ A.V _ A.hV2.toMulAction a).symm
    · simp only [h.neg_one_pow, neg_one_smul, TensorProduct.tmul_neg]

def rationalizeGroupHomologyIso (A : Rep.{0} ℤ G) (n : ℕ) :
    groupHomology (rationalizeRepresentation A) n ≅
      ModuleCat.of ℚ (ℚ ⊗[ℤ] groupHomology A n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).mapIso
    (rationalizeGroupChainsIso A).symm ≪≫
      rationalModuleHomologyIso (groupHomology.inhomogeneousChains A) n

end PolycyclicRecognition

end

end OAI
