import OAI.Analysis.Pureness.Tensor.SpatialRepresentationIndependence
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped TensorProduct InnerProductSpace
variable {A B H K : Type*} [CStarAlgebra A] [CStarAlgebra B]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))

lemma spatial_relation_coefficients_zero
    (hα : Function.Injective α) (hβ : Function.Injective β)
    {ι : Type*} (b : ι → B) (hb : LinearIndependent ℂ b)
    (s : Finset ι) (a : ι → A)
    (hz : spatialStarTensorHom α β (∑ i ∈ s, a i ⊗ₜ[ℂ] b i) = 0) :
    ∀ i ∈ s, a i = 0 := by
  classical
  have hc (x x' : H) : ∑ i ∈ s, ⟪x', α (a i) x⟫_ℂ • b i = 0 := by
    apply (map_eq_zero_iff β hβ).mp
    apply ContinuousLinearMap.ext
    intro y
    apply ext_inner_left ℂ
    intro y'
    have he := congrArg (fun T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K =>
      ⟪((x' ⊗ₜ[ℂ] y' : H ⊗[ℂ] K) : SpatialHilbert H K), T (x ⊗ₜ[ℂ] y : H ⊗[ℂ] K)⟫_ℂ) hz
    simpa only [map_sum, map_smul, spatialStarTensorHom_tmul,
      sum_apply, smul_apply,
      zero_apply, inner_zero_right, inner_sum, inner_smul_right,
      spatialTensorOp_coe, TensorProduct.mapL_tmul, UniformSpace.Completion.inner_coe,
      TensorProduct.inner_tmul] using he
  intro i hi
  apply (map_eq_zero_iff α hα).mp
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro x'
  rw [zero_apply, inner_zero_right]
  exact (linearIndependent_iff'.mp hb) s _ (hc x x') i hi

theorem spatialStarTensorHom_injective_of_faithful
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    Function.Injective (spatialStarTensorHom α β) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  let b := Module.Free.chooseBasis ℂ B
  obtain ⟨a, rfl⟩ := TensorProduct.eq_repr_basis_right b z
  have ha := spatial_relation_coefficients_zero α β hα hβ b b.linearIndependent a.support a hz
  change ∑ i ∈ a.support, a i ⊗ₜ[ℂ] b i = 0
  apply Finset.sum_eq_zero
  intro i hi
  rw [ha i hi, TensorProduct.zero_tmul]
end CuntzPureness

end

end OAI
