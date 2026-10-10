import OAI.Algebra.Finitistic.Localization.BoundedQuotientGenerators
import OAI.Algebra.Finitistic.Localization.EvaluationFromAlgebra
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.CategoryTheory.Localization.Linear

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.QuadraticEncoding
open Representation IdempotentTensor FiniteProjectiveHomotopy
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

instance boundedKLinear : Linear k (BoundedK P) := inferInstance
instance boundedQLinear : Linear k (BoundedQ P) := inferInstance

lemma pathMap_target (z : Paths k d) : vertexId (P := P) 2 * pathMap P z = pathMap P z := by
  change ThreeVertexAlgebra.mul (composition P) (0,0,1,0,0,0)
    (0,0,0,0,0,(relationSpace P).mkQ z) = _
  simp [ThreeVertexAlgebra.mul, pathMap, lengthTwo]

/-- Left multiplication by a length-two path, as a linear family of module maps. -/
def pathModuleMap : Paths k d →ₗ[k] (vertexModule P 0 ⟶ vertexModule P 2) where
  toFun z := ModuleCat.ofHom (leftMultiply (pathMap P z) (pathMap_target P z))
  map_add' z w := by
    ext m : 2
    apply Subtype.ext
    change pathMap P (z+w) * m.val = pathMap P z * m.val + pathMap P w * m.val
    rw [map_add, add_mul]
  map_smul' c z := by
    ext m : 2
    apply Subtype.ext
    change pathMap P (c • z) * m.val = (pathMap P z * m.val) * algebraMap k (B P) c
    rw [map_smul, smul_mul_assoc, Algebra.smul_def, Algebra.commutes]

lemma pathModuleMap_basis (h l : Fin (d+1)) :
    pathModuleMap P (basis h ⊗ₜ[k] basis l) = arrowModule01 P l ≫ arrowModule12 P h := by
  ext m : 2
  apply Subtype.ext
  change pathMap P (basis h ⊗ₜ[k] basis l) * m.val = arrow12 P h * (arrow01 P l * m.val)
  rw [← arrow_product, mul_assoc]

instance degreeZeroAdditive : (degreeZero P).Additive := by
  dsimp [degreeZero]
  infer_instance
instance degreeZeroLinear : (degreeZero P).Linear k :=
  inferInstanceAs ((CochainComplex.singleFunctor (ModuleCat.{u} (B P)ᵐᵒᵖ) 0).Linear k)

def vertexHomEquiv (i j : Fin 3) : (vertexK P i ⟶ vertexK P j) ≃ₗ[k]
    ((inclusion (B P)ᵐᵒᵖ).obj (vertexK P i) ⟶ (inclusion (B P)ᵐᵒᵖ).obj (vertexK P j)) :=
  LinearEquiv.ofBijective ((inclusion (B P)ᵐᵒᵖ).mapLinearMap k)
    ⟨(inclusion (B P)ᵐᵒᵖ).map_injective, (inclusion (B P)ᵐᵒᵖ).map_surjective⟩

/-- Transport module maps to the concrete degree-zero objects of K. -/
def vertexHomMap (i j : Fin 3) :
    (vertexModule P i ⟶ vertexModule P j) →ₗ[k] (vertexK P i ⟶ vertexK P j) :=
  (vertexHomEquiv P i j).symm.toLinearMap.comp
      (((HomotopyCategory.quotient _ _).mapLinearMap k).comp ((degreeZero P).mapLinearMap k))

lemma vertexHomMap_eq (i j : Fin 3) (f : vertexModule P i ⟶ vertexModule P j) :
    vertexHomMap P i j f = (inclusion (B P)ᵐᵒᵖ).preimage
      ((HomotopyCategory.quotient _ _).map ((degreeZero P).map f)) := by
  apply (inclusion (B P)ᵐᵒᵖ).map_injective
  erw [Functor.map_preimage]
  exact (vertexHomEquiv P i j).apply_symm_apply _

lemma vertexHomMap_comp {i j l : Fin 3} (f : vertexModule P i ⟶ vertexModule P j)
    (g : vertexModule P j ⟶ vertexModule P l) :
    vertexHomMap P i l (f ≫ g) = vertexHomMap P i j f ≫ vertexHomMap P j l g := by
  rw [vertexHomMap_eq,vertexHomMap_eq,vertexHomMap_eq]
  apply (inclusion (B P)ᵐᵒᵖ).map_injective
  erw [(inclusion (B P)ᵐᵒᵖ).map_comp]
  erw [Functor.map_preimage,Functor.map_preimage,Functor.map_preimage]
  rw [(degreeZero P).map_comp]
  exact (HomotopyCategory.quotient _ _).map_comp _ _

def pathQMap : Paths k d →ₗ[k] (vertexQ P 0 ⟶ vertexQ P 2) :=
  ((boundedDenominators P).Q.mapLinearMap k).comp
    ((vertexHomMap P 0 2).comp (pathModuleMap P))

lemma pathQMap_basis (h l : Fin (d+1)) :
    pathQMap P (basis h ⊗ₜ[k] basis l) = arrowQ01 P l ≫ arrowQ12 P h := by
  change (boundedDenominators P).Q.map
    (vertexHomMap P 0 2 (pathModuleMap P (basis h ⊗ₜ[k] basis l))) = _
  rw [pathModuleMap_basis,vertexHomMap_comp,Functor.map_comp,vertexHomMap_eq,vertexHomMap_eq]
  rfl

lemma pathModuleMap_kills (z : Paths k d) (hz : z ∈ relationSpace P) : pathModuleMap P z = 0 := by
  ext m : 2
  apply Subtype.ext
  change pathMap P z * m.val = 0
  rw [(pathMap_eq_zero_iff P z).mpr hz,zero_mul]

lemma pathQMap_kills (z : Paths k d) (hz : z ∈ relationSpace P) : pathQMap P z = 0 := by
  change (boundedDenominators P).Q.map (vertexHomMap P 0 2 (pathModuleMap P z)) = 0
  rw [pathModuleMap_kills P z hz,map_zero,Functor.map_zero]

lemma quotient_commutation (h : Fin d) :
    arrowQ01 P 0 ≫ arrowQ12 P h.succ = arrowQ01 P h.succ ≫ arrowQ12 P 0 := by
  have hz := pathQMap_kills P (commutation h)
    (Submodule.subset_span (Or.inl ⟨h,rfl⟩))
  simpa only [commutation,map_sub,pathQMap_basis,sub_eq_zero] using hz

lemma quotient_homogenized (j : Fin t) :
    (∑ h, ∑ l, P.quadratic j h l • (arrowQ01 P l.succ ≫ arrowQ12 P h.succ)) +
    (∑ h, P.linear j h • (arrowQ01 P h.succ ≫ arrowQ12 P 0)) +
    P.constant j • (arrowQ01 P 0 ≫ arrowQ12 P 0) = 0 := by
  have hz := pathQMap_kills P (homogenized P j)
    (Submodule.subset_span (Or.inr ⟨j,rfl⟩))
  simpa only [homogenized,map_add,map_sum,map_smul,pathQMap_basis] using hz
end LittleFinitistic.QuadraticEncoding

end

end OAI
