import OAI.Analysis.Pureness.Tensor.SpatialGroupConjugation
import OAI.Analysis.Pureness.GroupAlgebra.FreeGroupPowersPartition
import OAI.Analysis.Pureness.GroupAlgebra.PowersAveraging
import OAI.Analysis.Pureness.Operators.UnitaryAverageFunctor

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped TensorProduct
local instance spatialPowersPolynomialDecidableEq {X : Type*} : DecidableEq X := Classical.decEq X
variable {A H : Type*} [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H))

def spatialFreeGroupAverage (m n : ℕ)
    (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype) :=
  unitaryAverage (B := representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype) (fun i : Fin n => spatialGroupUnitary α (FreeGroup.of (m+i.val))) x

lemma spatialGroupPolynomialMap_val (a : FreeGroup ℕ →₀ A) :
    (spatialGroupPolynomialMap (G := FreeGroup ℕ) α a).val =
      ∑ g ∈ a.support, spatialTensorOp (α (a g)) (groupLeft g) := by
  change (representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype).subtype
    (spatialGroupPolynomialMap (G := FreeGroup ℕ) α a) = _
  refine (congrArg (representedSpatialTensor α
    (reducedGroupAlgebra (FreeGroup ℕ)).subtype).subtype
    (spatialGroupPolynomialMap_apply (G := FreeGroup ℕ) α a)).trans ?_
  refine (map_sum (representedSpatialTensor α
    (reducedGroupAlgebra (FreeGroup ℕ)).subtype).subtype _ _).trans ?_
  apply Finset.sum_congr rfl
  intro g hg
  change spatialStarTensorHom α (reducedGroupAlgebra (FreeGroup ℕ)).subtype
    (a g ⊗ₜ[ℂ] (reducedGroupUnitary (FreeGroup ℕ) g : reducedGroupAlgebra (FreeGroup ℕ))) = _
  exact spatialStarTensorHom_tmul _ _ _ _

lemma spatialPowers_polynomial_corner_zero (m : ℕ) (a : FreeGroup ℕ →₀ A)
    (ha : a 1 = 0) (hs : ∀ g ∈ a.support, g ∈ initialFreeSubgroup m) :
    spatialCoordinateProjection (H := H) (freeGroupPowersC m)*
      (spatialGroupPolynomialMap (G := FreeGroup ℕ) α a).val*
      spatialCoordinateProjection (H := H) (freeGroupPowersC m) = 0 := by
  rw [spatialGroupPolynomialMap_val,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro g hg
  have hg1 : g ≠ 1 := by
    intro he; subst g
    exact (Finsupp.mem_support_iff.mp hg) ha
  exact spatialCoordinateProjection_tensor_zero (freeGroupPowersC m) g
    (fun h hh => freeGroupPowersC_old_disjoint m g (hs g hg) hg1 h hh) (α (a g))

private lemma spatialPowers_supports_orthogonal (m : ℕ) {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) :
    let v := fun k => spatialRightOperator (H := H) (groupLeft (FreeGroup.of (m+k)))
    let p := spatialCoordinateProjection (H := H) (freeGroupPowersC m)ᶜ
    (v i.val*p*star (v i.val))*(v j.val*p*star (v j.val)) = 0 := by
  dsimp only
  rw [spatialCoordinateProjection_conjugate, spatialCoordinateProjection_conjugate]
  apply spatialCoordinateProjection_disjoint
  apply freeGroupPowers_complement_images_disjoint m (m+i.val) (m+j.val)
    (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  intro he
  exact hij (Fin.ext (Nat.add_left_cancel he))

theorem spatialFreeGroupAverage_polynomial_bound (m n : ℕ) (a : FreeGroup ℕ →₀ A)
    (ha : a 1 = 0) (hs : ∀ g ∈ a.support, g ∈ initialFreeSubgroup m) :
    ‖spatialFreeGroupAverage α m n (spatialGroupPolynomialMap (G := FreeGroup ℕ) α a)‖ ≤
      (n : ℝ)⁻¹*(2*Real.sqrt n*‖spatialGroupPolynomialMap (G := FreeGroup ℕ) α a‖) := by
  let Q := representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype
  let u : Fin n → unitary (SpatialHilbert H (GroupL2 (FreeGroup ℕ)) →L[ℂ] SpatialHilbert H (GroupL2 (FreeGroup ℕ))) := fun i : Fin n => Unitary.map (StarMonoidHom.ofClass Q.subtype)
    (spatialGroupUnitary α (FreeGroup.of (m+i.val)))
  have hu (i : Fin n) : (u i : SpatialHilbert H (GroupL2 (FreeGroup ℕ)) →L[ℂ]
      SpatialHilbert H (GroupL2 (FreeGroup ℕ))) =
      spatialRightOperator (H := H) (groupLeft (FreeGroup.of (m+i.val))) :=
    spatialGroupUnitary_val α _
  let p := spatialCoordinateProjection (H := H) (freeGroupPowersC m)ᶜ
  have hpc : 1-p = spatialCoordinateProjection (H := H) (freeGroupPowersC m) := by
    exact (spatialCoordinateProjection_compl (H := H) (freeGroupPowersC m)ᶜ).symm.trans
      (congrArg (spatialCoordinateProjection (H := H)) (compl_compl _))
  have hb := powers_unitaryAverage_bound (B := SpatialHilbert H (GroupL2 (FreeGroup ℕ)) →L[ℂ] SpatialHilbert H (GroupL2 (FreeGroup ℕ))) u p (spatialGroupPolynomialMap (G := FreeGroup ℕ) α a).val
    (spatialCoordinateProjection_star (H := H) (freeGroupPowersC m)ᶜ)
    (spatialCoordinateProjection_norm_le (H := H) (freeGroupPowersC m)ᶜ)
    ((congrArg norm hpc).trans_le
      (spatialCoordinateProjection_norm_le (H := H) (freeGroupPowersC m)))
    ((congrArg (fun q => q * (spatialGroupPolynomialMap (G := FreeGroup ℕ) α a).val * q)
      hpc).trans (spatialPowers_polynomial_corner_zero α m a ha hs)) ?_
  · have hv := congrArg norm (unitaryAverage_starHom_map
      (B := Q) (E := SpatialHilbert H (GroupL2 (FreeGroup ℕ)) →L[ℂ] SpatialHilbert H (GroupL2 (FreeGroup ℕ)))
      Q.subtype (fun i : Fin n => spatialGroupUnitary α (FreeGroup.of (m+i.val)))
      (spatialGroupPolynomialMap (G := FreeGroup ℕ) α a))
    exact hv.trans_le hb

  · intro i j hij
    refine (congrArg₂ (fun v w => (v*p*star v)*(w*p*star w)) (hu i) (hu j)).trans ?_
    exact spatialPowers_supports_orthogonal (H := H) m i j hij
end CuntzPureness

end

end OAI
