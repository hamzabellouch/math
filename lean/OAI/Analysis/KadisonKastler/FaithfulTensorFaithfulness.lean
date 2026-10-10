import OAI.Analysis.KadisonKastler.FaithfulCyclicTensor

namespace OAI

/-! # Faithfulness of the tensor restriction

Vector slices of a positive product operator lie in the original algebra.
The faithful cyclic compression detects each such slice. Applying this to
T* T proves faithfulness on the whole spatial von Neumann product.
-/

namespace KadisonKastler

open UnitalTomsWinter
open scoped TensorProduct

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem tensorVectorSlice_eq_zero_of_faithfulTensorHom_eq_zero
    (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    (T : Algebra (spatialProductAlgebra M D)) (hT : faithfulTensorHom M D T = 0) (ξ : K) :
    tensorVectorSlice ξ T.val = 0 := by
  let a : Algebra M := ⟨tensorVectorSlice ξ T.val, tensorVectorSlice_mem M D ξ T.val T.property⟩
  have ha : faithfulCyclicHom M a = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    apply (faithfulCyclicSpace M).subtype_injective
    change ((faithfulCyclicHom M a x : faithfulCyclicSpace M) : CountableHilbertSum H) = 0
    rw [faithfulCyclicHom_apply]
    change l2Diagonal (tensorVectorSlice ξ T.val) x.val = 0
    ext n
    have hz := faithfulTensorHom_intertwines M D T
      ((x ⊗ₜ[ℂ] ξ : faithfulCyclicSpace M ⊗[ℂ] K) :
        SpatialHilbert (faithfulCyclicSpace M) K)
    rw [hT, zero_apply, map_zero] at hz
    have h := congrArg (fun z : CountableHilbertSum (SpatialHilbert H K) => z n) hz
    rw [faithfulTensorEmbedding_tmul] at h
    change 0 = T.val (tensorVector ξ (x.val n)) at h
    change (tensorVector ξ).adjoint (T.val (tensorVector ξ (x.val n))) = 0
    rw [← h, map_zero]
  have hz : a = 0 := (faithfulCyclicHom_injective M) (by simpa only [map_zero] using ha)
  exact congrArg Subtype.val hz

theorem faithfulTensorHom_injective (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K) :
    Function.Injective (faithfulTensorHom M D) := by
  apply (injective_iff_map_eq_zero (faithfulTensorHom M D)).mpr
  intro a ha
  let b : Algebra (spatialProductAlgebra M D) := star a * a
  have hs : faithfulTensorHom M D b = 0 := by
    calc
      faithfulTensorHom M D b = faithfulTensorHom M D (star a) * faithfulTensorHom M D a :=
        (faithfulTensorHom M D).map_mul (star a) a
      _ = faithfulTensorHom M D (star a) * 0 := congrArg (fun T => faithfulTensorHom M D (star a) * T) ha
      _ = 0 := mul_zero _
  have hslice (ξ : K) : tensorVectorSlice ξ (star a.val * a.val) = 0 :=
    tensorVectorSlice_eq_zero_of_faithfulTensorHom_eq_zero M D b hs ξ
  apply Subtype.ext
  apply spatialTensorOp_ext
  intro x ξ
  change a.val (tensorVector ξ x) = 0
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  have h := congrArg (fun S : H →L[ℂ] H => inner ℂ x (S x)) (hslice ξ)
  change inner ℂ x ((tensorVector ξ).adjoint
    ((star a.val) (a.val (tensorVector ξ x)))) = inner ℂ x 0 at h
  rw [ContinuousLinearMap.star_eq_adjoint, inner_zero_right] at h
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right] at h
  exact h

theorem faithfulTensorHom_norm (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    (a : Algebra (spatialProductAlgebra M D)) : ‖faithfulTensorHom M D a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (faithfulTensorHom M D) (faithfulTensorHom_injective M D) a

end

end KadisonKastler

end OAI
