import OAI.Analysis.Pureness.Tensor.SpatialGroupMatrixSlices
import OAI.Analysis.Pureness.Tensor.SpatialSliceCompression
import OAI.Analysis.Pureness.Tensor.SpatialHilbertBasisDensity

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped TensorProduct InnerProductSpace
local instance spatialExpectationFaithfulDecidableEq {X : Type*} : DecidableEq X := Classical.decEq X
variable {A H G : Type*} [Group G] [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hα : Function.Injective α)

include hα in

lemma spatialGroupFourier_diagonal (g : G)
    (x : representedSpatialTensor α (reducedGroupAlgebra G).subtype) :
    α (spatialGroupFourier α (1 : G) x) =
      (spatialRightVector (H := H) (lp.single 2 g (1 : ℂ))).adjoint.comp
        (x.val.comp (spatialRightVector (lp.single 2 g (1 : ℂ)))) := by
  have hm := spatialGroupMatrixSlice_eq_fourier α hα g g x
  have he := congrArg (fun k : G => spatialGroupFourier α k x) (mul_inv_cancel g)
  exact (congrArg α (hm.trans he)).symm.trans
    (spatialVectorSlice_compression α hα (reducedGroupAlgebra G).subtype
      (lp.single 2 g 1) (lp.single 2 g 1) x)

include hα in
lemma spatialGroupFourier_square_inner (g : G) (v : H)
    (x : representedSpatialTensor α (reducedGroupAlgebra G).subtype) :
    ⟪v, α (spatialGroupFourier α (1 : G) (star x*x)) v⟫_ℂ =
      (‖x.val (spatialRightVector (lp.single 2 g (1 : ℂ)) v)‖ ^ 2 : ℝ) := by
  rw [spatialGroupFourier_diagonal α hα g]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  change ⟪spatialRightVector (lp.single 2 g (1 : ℂ)) v,
    x.val.adjoint (x.val (spatialRightVector (lp.single 2 g (1 : ℂ)) v))⟫_ℂ = _
  rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
  rfl

omit [Group G] [CompleteSpace H] in
lemma spatialOperator_eq_zero_of_delta
    (S : SpatialHilbert H (GroupL2 G) →L[ℂ] SpatialHilbert H (GroupL2 G))
    (hS : ∀ (v : H) (g : G), S (spatialRightVector (lp.single 2 g (1 : ℂ)) v) = 0) :
    S = 0 := by
  have ht (v : H) (w : GroupL2 G) :
      S ((v ⊗ₜ[ℂ] w : H ⊗[ℂ] GroupL2 G) : SpatialHilbert H (GroupL2 G)) = 0 := by
    let R := S.comp (spatialLeftVector v)
    have hs : Submodule.span ℂ (Set.range (fun g : G => (lp.single 2 g 1 : GroupL2 G))) ≤
        LinearMap.ker R.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g, rfl⟩
      change S (spatialLeftVector v (lp.single 2 g 1)) = 0
      rw [spatialLeftVector_apply]
      exact hS v g
    have hw := closure_minimal hs R.isClosed_ker (groupDelta_dense G w)
    change S (spatialLeftVector v w) = 0 at hw
    simpa only [spatialLeftVector_apply] using hw
  apply ContinuousLinearMap.ext
  intro z
  change S z = 0
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq S.continuous continuous_const
  | ih z =>
    induction z using TensorProduct.inductionOn with
    | tmul v w => exact ht v w
    | add z w hz hw => simp only [UniformSpace.Completion.coe_add, map_add, hz, hw, add_zero]

include hα in

theorem spatialGroupFourier_square_eq_zero_iff
    (x : representedSpatialTensor α (reducedGroupAlgebra G).subtype) :
    spatialGroupFourier α (1 : G) (star x*x) = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply Subtype.ext
    change x.val = 0
    apply spatialOperator_eq_zero_of_delta
    intro v g
    have hi := spatialGroupFourier_square_inner α hα g v x
    rw [hx, map_zero, zero_apply, inner_zero_right] at hi
    have hn : ‖x.val (spatialRightVector (lp.single 2 g (1 : ℂ)) v)‖ ^ 2 = 0 := by
      exact_mod_cast hi.symm
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  · rintro rfl
    simp
end CuntzPureness

end

end OAI
