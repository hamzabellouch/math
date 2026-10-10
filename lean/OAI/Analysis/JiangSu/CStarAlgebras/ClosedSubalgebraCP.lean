import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CStarAlgebras.StateCoefficientApproximation
import OAI.Analysis.JiangSu.CStarAlgebras.FourEdgeGroupSurgery

namespace OAI

section

noncomputable section
namespace ClosedSubalgebraCP
open scoped CStarAlgebra ComplexOrder

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
lemma nonneg_of_injective (π : A →⋆ₐ[ℂ] B) (hi : Function.Injective π)
    (a : A) (ha : 0≤π a) : 0≤a := by
  have hs : IsSelfAdjoint a := by
    change star a=a
    apply hi
    rw [map_star,ha.isSelfAdjoint.star_eq]
  let g : ℝ→ℝ := fun t => max t 0
  have hp : 0≤cfc g a := cfc_nonneg (fun _ _ => le_max_right _ _)
  have he : cfc g (π a)=π a := by
    conv_rhs => rw [←cfc_id' ℝ (π a)]
    apply cfc_congr
    intro x hx
    exact max_eq_left (spectrum_nonneg_of_nonneg ha hx)
  have hm : π (cfc g a)=cfc g (π a) := π.map_cfc g a (by fun_prop) (by fun_prop) hs ha.isSelfAdjoint
  have hx : cfc g a=a := hi (hm.trans he)
  rwa [hx] at hp

 def matrixMap (π : A →⋆ₐ[ℂ] B) {n : Type*} [Fintype n] [DecidableEq n] :
    CStarMatrix n n A →⋆ₐ[ℂ] CStarMatrix n n B where
  toFun M := M.map π
  map_zero' := map_zero (CStarMatrix.mapₙₐ (n := n) π.toNonUnitalStarAlgHom)
  map_one' := by ext i j; by_cases hij : i=j <;> simp [CStarMatrix.map_apply,CStarMatrix.one_apply,hij]
  map_add' M N := map_add (CStarMatrix.mapₙₐ (n := n) π.toNonUnitalStarAlgHom) M N
  map_mul' M N := map_mul (CStarMatrix.mapₙₐ (n := n) π.toNonUnitalStarAlgHom) M N
  commutes' z := by
    ext i j
    by_cases hij : i=j
    · simp only [CStarMatrix.map_apply,CStarMatrix.algebraMap_apply,hij,ite_true]
      exact π.commutes z
    · simp [CStarMatrix.map_apply,CStarMatrix.algebraMap_apply,hij]
  map_star' M := map_star (CStarMatrix.mapₙₐ (n := n) π.toNonUnitalStarAlgHom) M
lemma matrixMap_injective (π : A →⋆ₐ[ℂ] B) (hi : Function.Injective π)
    {n : Type*} [Fintype n] [DecidableEq n] : Function.Injective (matrixMap (n := n) π) := by
  intro M N he
  ext i j
  apply hi
  exact congrArg (fun X : CStarMatrix n n B => X i j) he

variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
 def reflect (π : A →⋆ₐ[ℂ] B) (hi : Function.Injective π) (φ : D→CP B)
    (ψ : D →ₗ[ℂ] A) (hψ : ∀ a,π (ψ a)=φ a) : D→CP A where
  toLinearMap := ψ
  map_cstarMatrix_nonneg' k M hM := by
    apply nonneg_of_injective (matrixMap π) (matrixMap_injective π hi)
    have he : matrixMap π (M.map ψ)=M.map φ := by ext i j; exact hψ _
    rw [he]
    exact φ.map_cstarMatrix_nonneg M hM

end ClosedSubalgebraCP

end
end

end OAI
