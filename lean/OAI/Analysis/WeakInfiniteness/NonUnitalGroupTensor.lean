import Mathlib
import OAI.Analysis.WeakInfiniteness.TensorHilbertSum

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

namespace WeakPureInfiniteness

section NonUnitalGroup

variable {A B G : Type*} [CStarAlgebra A] [CStarAlgebra B] [Group G]

def completedGroupOperator (φ : A →⋆ₙₐ[ℂ] B) (u : G →* unitary A) (g : G) : B :=
  φ (u g) + (1 - φ 1)

lemma completedGroupOperator_one (φ : A →⋆ₙₐ[ℂ] B) (u : G →* unitary A) :
    completedGroupOperator φ u 1 = 1 := by
  simp [completedGroupOperator]

lemma completedGroupOperator_mul (φ : A →⋆ₙₐ[ℂ] B) (u : G →* unitary A) (g h : G) :
    completedGroupOperator φ u (g * h) =
      completedGroupOperator φ u g * completedGroupOperator φ u h := by
  have hx (a : A) : φ a * (1 - φ 1) = 0 := by
    rw [mul_sub, mul_one, ← map_mul, mul_one, sub_self]
  have hy (a : A) : (1 - φ 1) * φ a = 0 := by
    rw [sub_mul, one_mul, ← map_mul, one_mul, sub_self]
  have hc : (1 - φ 1) * (1 - φ 1) = 1 - φ 1 := by
    rw [mul_sub, mul_one, hy, sub_zero]
  simp only [completedGroupOperator, map_mul, Submonoid.coe_mul, add_mul, mul_add,
    hx, hy, hc, add_zero, zero_add]

lemma completedGroupOperator_inv (φ : A →⋆ₙₐ[ℂ] B) (u : G →* unitary A) (g : G) :
    completedGroupOperator φ u g⁻¹ = star (completedGroupOperator φ u g) := by
  simp only [completedGroupOperator, map_inv, ← Unitary.star_eq_inv, Unitary.coe_star,
    map_star, star_add, star_sub, star_one]
  have hφ : star (φ 1) = φ 1 := by rw [← map_star, star_one]
  rw [hφ]

lemma completedGroupOperator_unitary (φ : A →⋆ₙₐ[ℂ] B) (u : G →* unitary A) (g : G) :
    completedGroupOperator φ u g ∈ unitary B := by
  constructor
  · rw [← completedGroupOperator_inv, ← completedGroupOperator_mul,
      inv_mul_cancel, completedGroupOperator_one]
  · rw [← completedGroupOperator_inv, ← completedGroupOperator_mul,
      mul_inv_cancel, completedGroupOperator_one]

def completedGroupUnitary (φ : A →⋆ₙₐ[ℂ] B) (u : G →* unitary A) : G →* unitary B where
  toFun g := ⟨completedGroupOperator φ u g, completedGroupOperator_unitary φ u g⟩
  map_one' := Subtype.ext (completedGroupOperator_one φ u)
  map_mul' g h := Subtype.ext (completedGroupOperator_mul φ u g h)

lemma projection_mul_completedGroup (φ : A →⋆ₙₐ[ℂ] B) (u : G →* unitary A) (g : G) :
    φ 1 * completedGroupOperator φ u g = φ (u g) := by
  simp only [completedGroupOperator, mul_add, mul_sub, mul_one, ← map_mul,
    one_mul, sub_self, add_zero]

end NonUnitalGroup

theorem norm_freeTensor_nonunital_sum_le {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (u : FreeTwo →* unitary A) :
    ‖∑ s : FreeLetter, TensorProduct.mapL (φ (u (freeLetter s)))
      (leftRegular (freeLetter s) : GroupHilbert FreeTwo →L[ℂ] GroupHilbert FreeTwo)‖ ≤
      2 * Real.sqrt 3 := by
  let π : FreeTwo →* H ≃ₗᵢ[ℂ] H :=
    Unitary.linearIsometryEquiv.toMonoidHom.comp (completedGroupUnitary φ u)
  let T := ∑ s : FreeLetter, TensorProduct.mapL
    (π (freeLetter s)).toContinuousLinearEquiv.toContinuousLinearMap
    (leftRegular (freeLetter s) : GroupHilbert FreeTwo →L[ℂ] GroupHilbert FreeTwo)
  have he : (∑ s : FreeLetter, TensorProduct.mapL (φ (u (freeLetter s)))
      (leftRegular (freeLetter s) : GroupHilbert FreeTwo →L[ℂ] GroupHilbert FreeTwo)) =
      ((φ 1).rTensor (GroupHilbert FreeTwo)).comp T := by
    apply ContinuousLinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul ξ η =>
      simp only [T, sum_apply, TensorProduct.mapL_tmul, ContinuousLinearMap.comp_apply,
        map_sum, ContinuousLinearMap.rTensor_tmul]
      apply Finset.sum_congr rfl
      intro s _
      congr 1
      exact (congrArg (fun f : H →L[ℂ] H => f ξ)
        (projection_mul_completedGroup φ u (freeLetter s))).symm
    | add z w hz hw => simp only [map_add, hz, hw]
  rw [he]
  have hp : ‖(φ 1).rTensor (GroupHilbert FreeTwo)‖ ≤ 1 := by
    apply (ContinuousLinearMap.norm_rTensor_le _ _).trans
    apply (NonUnitalStarAlgHom.norm_apply_le φ 1).trans
    cases subsingleton_or_nontrivial A with
    | inl h => simp [Subsingleton.elim (1 : A) 0]
    | inr h => simp
  have ht : ‖T‖ ≤ 2 * Real.sqrt 3 := norm_freeTensor_sum_le π
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by
      simpa only [one_mul] using mul_le_mul hp ht
        (ContinuousLinearMap.opNorm_nonneg T) zero_le_one)

end WeakPureInfiniteness
end

end OAI
