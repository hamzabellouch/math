import OAI.Analysis.OperatorAlgebra.GNSCyclicRepresentation

namespace OAI

/-! The cyclic GNS subrepresentation of a separable algebra is separable,
even when the original Hilbert representation is not. -/
noncomputable section
open TopologicalSpace
open scoped ComplexOrder
namespace WeakPureInfiniteness

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def gnsVectorLinear (f : A →ₚ[ℂ] ℂ) : A →ₗ[ℂ] gnsHilbert f where
  toFun := gnsVector f
  map_add' a b := by
    change ((f.toPreGNS (a + b) : f.PreGNS) : f.GNS) = _
    rw [map_add, UniformSpace.Completion.coe_add]
    rfl
  map_smul' c a := by
    change ((f.toPreGNS (c • a) : f.PreGNS) : f.GNS) = _
    rw [map_smul, UniformSpace.Completion.coe_smul]
    rfl

lemma gnsVector_norm_le (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hf : ∀ a, f a = inner ℂ ξ (π a ξ)) (a : A) :
    ‖gnsVector f a‖ ≤ ‖ξ‖ * ‖a‖ := by
  calc
    _ = ‖cyclicBundledGNSIsometry f π ξ hf (gnsVector f a)‖ :=
      ((cyclicBundledGNSIsometry f π ξ hf).norm_map _).symm
    _ = ‖π a ξ‖ := congrArg norm (cyclicBundledGNSIsometry_vector f π ξ hf a)
    _ ≤ ‖π a‖ * ‖ξ‖ := (π a).le_opNorm ξ
    _ ≤ ‖a‖ * ‖ξ‖ := mul_le_mul_of_nonneg_right
      (NonUnitalStarAlgHom.norm_apply_le π.toNonUnitalStarAlgHom a) (norm_nonneg ξ)
    _ = _ := mul_comm _ _

def gnsVectorContinuous (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hf : ∀ a, f a = inner ℂ ξ (π a ξ)) : A →L[ℂ] gnsHilbert f :=
  (gnsVectorLinear f).mkContinuous ‖ξ‖ (gnsVector_norm_le f π ξ hf)

lemma gnsVector_dense (f : A →ₚ[ℂ] ℂ) : DenseRange (gnsVector f) := by
  intro x
  refine gnsVector_induction_on f x isClosed_closure ?_
  intro a
  exact subset_closure ⟨a, rfl⟩

lemma gns_separable_of_cyclic [SeparableSpace A] (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hf : ∀ a, f a = inner ℂ ξ (π a ξ)) : SeparableSpace (gnsHilbert f) :=
  (gnsVector_dense f).separableSpace (gnsVectorContinuous f π ξ hf).continuous

end WeakPureInfiniteness

end

end OAI
