import OAI.Analysis.Pureness.Tensor.CommutingTensorClosure
import OAI.Analysis.Pureness.Comparison.SpatialTensorOperators

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped TensorProduct InnerProductSpace
variable {A B H K : Type*} [CStarAlgebra A] [CStarAlgebra B]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))

omit [CompleteSpace H] [CompleteSpace K] in
lemma spatialTensorOp_one : spatialTensorOp (1 : H →L[ℂ] H) (1 : K →L[ℂ] K) = 1 := by
  apply spatialTensorOp_ext
  intro x y
  simp

def spatialLeftHom : A →⋆ₐ[ℂ] (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) where
  toFun a := spatialTensorOp (α a) 1
  map_zero' := by simp
  map_one' := by rw [map_one,spatialTensorOp_one]
  map_add' a b := by rw [map_add,spatialTensorOp_add_left]
  map_mul' a b := by rw [map_mul,← spatialTensorOp_mul,mul_one]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,map_one,spatialTensorOp_smul_left,
      spatialTensorOp_one,Algebra.algebraMap_eq_smul_one]
  map_star' a := by rw [map_star,← spatialTensorOp_star,star_one]

def spatialRightHom : B →⋆ₐ[ℂ] (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) where
  toFun b := spatialTensorOp 1 (β b)
  map_zero' := by simp
  map_one' := by rw [map_one,spatialTensorOp_one]
  map_add' a b := by rw [map_add,spatialTensorOp_add_right]
  map_mul' a b := by rw [map_mul,← spatialTensorOp_mul,mul_one]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,map_one,spatialTensorOp_smul_right,
      spatialTensorOp_one,Algebra.algebraMap_eq_smul_one]
  map_star' b := by rw [map_star,← spatialTensorOp_star,star_one]

lemma spatialLeftRight_commute (a : A) (b : B) :
    Commute (spatialLeftHom (K := K) α a) (spatialRightHom (H := H) β b) := by
  change spatialTensorOp (α a) 1 * spatialTensorOp 1 (β b) =
    spatialTensorOp 1 (β b) * spatialTensorOp (α a) 1
  rw [← spatialTensorOp_mul,← spatialTensorOp_mul]
  simp

lemma spatialRightHom_injective [Nontrivial H] (hβ : Function.Injective β) :
    Function.Injective (spatialRightHom (H := H) β) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro b hb
  apply (map_eq_zero_iff β hβ).mp
  apply ContinuousLinearMap.ext
  intro y
  obtain ⟨x,hx⟩ := exists_ne (0 : H)
  have hz := congrArg (fun T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K =>
    ‖T (x ⊗ₜ[ℂ] y : H ⊗[ℂ] K)‖) hb
  simp only [zero_apply,norm_zero] at hz
  have hn : ‖x‖ * ‖β b y‖=0 := by simpa [spatialRightHom] using hz
  exact norm_eq_zero.mp ((mul_eq_zero.mp hn).resolve_left (norm_ne_zero_iff.mpr hx))

def spatialStarTensorHom :
    A ⊗[ℂ] B →⋆ₐ[ℂ] (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
  commutingStarTensorHom (N := SpatialHilbert H K →L[ℂ] SpatialHilbert H K) (spatialLeftHom (K := K) α) (spatialRightHom (H := H) β) (spatialLeftRight_commute α β)

lemma spatialStarTensorHom_tmul (a : A) (b : B) :
    spatialStarTensorHom α β (a ⊗ₜ[ℂ] b)=spatialTensorOp (α a) (β b) := by
  change spatialTensorOp (α a) 1 * spatialTensorOp 1 (β b) = _
  rw [← spatialTensorOp_mul,mul_one,one_mul]

lemma spatialStarTensorHom_injective [Nontrivial A] [Nontrivial H]
    (hsimple : TopologicallySimple A) (hβ : Function.Injective β) :
    Function.Injective (spatialStarTensorHom α β) :=
  commutingAlgTensorHom_injective hsimple
    (spatialLeftHom (K := K) α).toAlgHom (spatialRightHom (H := H) β).toAlgHom
    (spatialRightHom_injective (H := H) β hβ) (spatialLeftRight_commute α β)

abbrev representedSpatialTensor :=
  commutingTensorClosure (N := SpatialHilbert H K →L[ℂ] SpatialHilbert H K) (spatialLeftHom (K := K) α) (spatialRightHom (H := H) β) (spatialLeftRight_commute α β)

lemma representedSpatialTensor_dense :
    DenseRange (commutingTensorClosureMap (N := SpatialHilbert H K →L[ℂ] SpatialHilbert H K) (spatialLeftHom (K := K) α) (spatialRightHom (H := H) β)
      (spatialLeftRight_commute α β)) :=
  commutingTensorClosureMap_denseRange _ _ _
end CuntzPureness

end

end OAI
