import OAI.Analysis.IrrationalRotation.Operators.DenseOperatorRange
import OAI.Analysis.IrrationalRotation.Rotation.RotationInjective
import OAI.Analysis.IrrationalRotation.Rotation.Rotation

namespace OAI

noncomputable section

namespace Invariant233.Rotation

theorem representation_real_selfAdjoint (θ : ℝ) (f : C(Circle, ℝ)) :
    IsSelfAdjoint (representation θ (complexWeight f)) := by
  show star (representation θ (complexWeight f)) = representation θ (complexWeight f)
  rw [← representation_star]
  congr 1
  ext x
  simp [complexWeight]

theorem representation_real_denseRange (θ : ℝ) (f : C(Circle, ℝ))
    (hf : IsContinuousCircleWeight f) :
    DenseRange (representation θ (complexWeight f)) :=
  OperatorRange.denseRange_of_selfAdjoint_injective _
    (representation_real_selfAdjoint θ f) (representation_real_injective θ f hf)

theorem weightedReal_denseRange (θ : ℝ) (f : C(Circle, ℝ))
    (hf : IsContinuousCircleWeight f) : DenseRange (weightedReal θ f) :=
  (OperatorRange.unitary_mul_selfAdjoint_range U _ U_mem_unitary
    (representation_real_selfAdjoint θ f) (representation_real_injective θ f hf)).2

theorem weightedReal_not_surjective {θ : ℝ} (hθ : Irrational θ)
    (f : C(Circle, ℝ)) (hf : IsContinuousCircleWeight f) :
    ¬ Function.Surjective (weightedReal θ f) := by
  apply OperatorRange.not_surjective_of_zero_mem_spectrum _
    (weightedReal_injective θ f hf)
  rw [weightedReal_spectrum hθ f hf]
  exact Set.mem_singleton 0

theorem weightedReal_range_not_closed {θ : ℝ} (hθ : Irrational θ)
    (f : C(Circle, ℝ)) (hf : IsContinuousCircleWeight f) :
    ¬ IsClosed (Set.range (weightedReal θ f)) :=
  OperatorRange.not_isClosed_range_of_dense_not_surjective _
    (weightedReal_denseRange θ f hf) (weightedReal_not_surjective hθ f hf)

theorem weightedReal_eigenvector_eq_zero {θ : ℝ} (hθ : Irrational θ)
    (f : C(Circle, ℝ)) (hf : IsContinuousCircleWeight f)
    (z : ℂ) (ξ : Hilbert) (hξ : weightedReal θ f ξ = z • ξ) : ξ = 0 :=
  OperatorRange.eq_zero_of_eigenvector_of_spectrum_zero _
    (weightedReal_injective θ f hf) (weightedReal_spectrum hθ f hf) z ξ hξ

end Invariant233.Rotation

end

end OAI
