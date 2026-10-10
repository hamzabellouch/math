import OAI.Analysis.OperatorAlgebra.TracialSpatialState
import OAI.Analysis.OperatorAlgebra.TracialTensorVector

namespace OAI

/-! The finite tracial multiplication representation is continuous for the
spatial tensor norm when the represented von Neumann algebra admits a c.p.
expectation. -/

noncomputable section
open scoped TensorProduct InnerProductSpace ComplexOrder

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def subalgebraOppositeHom (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    Sᵐᵒᵖ →⋆ₐ[ℂ] (H →L[ℂ] H)ᵐᵒᵖ where
  __ := S.subtype.toAlgHom.op
  map_star' a := congrArg MulOpposite.op (map_star S.subtype a.unop)

def tracialSpatialTensor (M : VonNeumannAlgebra H) :
    M.toStarSubalgebra ⊗[ℂ] M.toStarSubalgebraᵐᵒᵖ →⋆ₐ[ℂ]
      (NuclearUltrapower.HilbertSchmidt H →L[ℂ] NuclearUltrapower.HilbertSchmidt H) :=
  Pureness.commutingStarTensorHom
    (densityLeftRepresentation.comp M.toStarSubalgebra.subtype)
    (densityRightRepresentation.comp (subalgebraOppositeHom M.toStarSubalgebra))
    (fun a b => densityLeftRight_commute (a : H →L[ℂ] H) (b.unop : H →L[ℂ] H))

@[simp] lemma tracialSpatialTensor_tmul (M : VonNeumannAlgebra H)
    (a b : M.toStarSubalgebra) :
    tracialSpatialTensor M (a ⊗ₜ[ℂ] MulOpposite.op b) =
      densityLeftRepresentation (a : H →L[ℂ] H) *
        densityRightRepresentation (MulOpposite.op (b : H →L[ℂ] H)) := rfl

variable (M : VonNeumannAlgebra H)
  [PartialOrder M.toStarSubalgebra] [StarOrderedRing M.toStarSubalgebra]
  (τ : Pureness.TracialState M.toStarSubalgebra)

def tracialMultiplicationTensor :
    M.toStarSubalgebra ⊗[ℂ] M.toStarSubalgebraᵐᵒᵖ →⋆ₐ[ℂ]
      (τ.functional.GNS →L[ℂ] τ.functional.GNS) :=
  traceTensor τ.functional τ.tracial

lemma tracialMultiplicationTensor_vector (a b : M.toStarSubalgebra) :
    tracialMultiplicationTensor M τ (a ⊗ₜ[ℂ] MulOpposite.op b)
        (τ.functional.toPreGNS 1 : τ.functional.GNS) =
      (τ.functional.toPreGNS (a * b) : τ.functional.GNS) :=
  traceTensor_vector τ.functional τ.tracial a b

lemma tracialMultiplicationTensor_cyclic :
    DenseRange (fun z => tracialMultiplicationTensor M τ z
      (τ.functional.toPreGNS 1 : τ.functional.GNS)) :=
  traceTensor_cyclic τ.functional τ.tracial

lemma tracial_multiplication_norm_le_of_state
    (φ : (NuclearUltrapower.HilbertSchmidt H →L[ℂ]
      NuclearUltrapower.HilbertSchmidt H) →ₚ[ℂ] ℂ)
    (hφ : ∀ a b : M.toStarSubalgebra,
      φ (densityLeftRepresentation (a : H →L[ℂ] H) *
        densityRightRepresentation (MulOpposite.op (b : H →L[ℂ] H))) =
          τ.functional (a * b))
    (z : M.toStarSubalgebra ⊗[ℂ] M.toStarSubalgebraᵐᵒᵖ) :
    ‖tracialMultiplicationTensor M τ z‖ ≤ ‖tracialSpatialTensor M z‖ := by
  have hp : ∀ a b : M.toStarSubalgebra,
      φ (tracialSpatialTensor M (a ⊗ₜ[ℂ] MulOpposite.op b)) = τ.functional (a * b) := by
    intro a b
    rw [tracialSpatialTensor_tmul]
    exact hφ a b
  change ‖traceTensor τ.functional τ.tracial z‖ ≤ ‖tracialSpatialTensor M z‖
  exact traceTensor_norm_le τ.functional τ.tracial (tracialSpatialTensor M) φ hp z

/-- The finite tracial part of the injectivity/semidiscreteness argument:
the diagonal multiplication representation is bounded by the spatial norm. -/
theorem tracial_multiplication_norm_le
    (E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (hE : CompletelyPositive E) (hEr : ∀ T, E T ∈ M)
    (hEf : ∀ T, T ∈ M → E T = T)
    (z : M.toStarSubalgebra ⊗[ℂ] M.toStarSubalgebraᵐᵒᵖ) :
    ‖tracialMultiplicationTensor M τ z‖ ≤ ‖tracialSpatialTensor M z‖ := by
  let hex := expectation_tracial_spatial_state (H := H) M τ E hE hEr hEf
  exact tracial_multiplication_norm_le_of_state M τ hex.choose hex.choose_spec.2 z

end WeakPureInfiniteness

end

end OAI
