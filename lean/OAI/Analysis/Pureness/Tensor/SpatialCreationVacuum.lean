import OAI.Analysis.Pureness.Tensor.SpatialPartialTranslations

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped TensorProduct CStarAlgebra
variable {A H : Type*} [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H))

def spatialVacuumVector (x : H) : SpatialHilbert H (GroupL2 (FreeGroup ℕ)) :=
  (x ⊗ₜ[ℂ] groupVacuum : H ⊗[ℂ] GroupL2 (FreeGroup ℕ))

omit [CompleteSpace H] in
lemma spatialVacuumVector_norm (x : H) : ‖spatialVacuumVector x‖ = ‖x‖ := by
  simp only [spatialVacuumVector, UniformSpace.Completion.norm_coe,
    TensorProduct.norm_tmul, groupVacuum_norm, mul_one]

theorem spatialFreeCreationSum_star_vacuum {n : ℕ} (a : Fin n → A) (x : H) :
    star (spatialFreeCreationSum α a) (spatialVacuumVector x) = 0 := by
  rw [spatialFreeCreationSum, star_sum (Finset.univ)
    (fun i : Fin n => spatialTensorOp (α (a i)) (freeCreation (i : ℕ)))]
  change (∑ i, star (spatialTensorOp (α (a i)) (freeCreation (i : ℕ)))) _ = 0
  rw [sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [← spatialTensorOp_star]
  simp only [spatialVacuumVector, spatialTensorOp_coe, TensorProduct.mapL_tmul,
    freeCreation_star_vacuum, TensorProduct.tmul_zero, UniformSpace.Completion.coe_zero]

theorem operator_not_isUnit_of_star_kills {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (T : K →L[ℂ] K) (x : K)
    (hx : x ≠ 0) (hT : star T x = 0) : ¬ IsUnit T := by
  intro ht
  obtain ⟨u, hu⟩ := ht.star
  have hi : (↑u⁻¹ : K →L[ℂ] K) * star T = 1 := by rw [← hu]; simp
  have hh := congrArg (fun S : K →L[ℂ] K => S x) hi
  simp only [mul_apply_eq_comp, hT, map_zero, one_apply_eq_self] at hh
  exact hx hh.symm

theorem spatialFreeCreationSum_not_isUnit [Nontrivial H] {n : ℕ} (a : Fin n → A) :
    ¬ IsUnit (spatialFreeCreationSum α a) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  apply operator_not_isUnit_of_star_kills _ (spatialVacuumVector x)
  · intro he
    have hh := congrArg norm he
    rw [spatialVacuumVector_norm, norm_zero] at hh
    exact hx (norm_eq_zero.mp hh)
  · exact spatialFreeCreationSum_star_vacuum α a x
end CuntzPureness

end

end OAI
