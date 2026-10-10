import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSamplingParameters

namespace OAI

/-! # Nonvanishing of the actual linear sampling weights -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The linear form underlying each actual sampling weight is nonzero. -/
theorem sampling_linear_weight_ne_zero (i : Fin M.letterCount) :
    (M.supportIn T hunimod eW).weight i ≠ 0 := by
  intro h
  exact M.sampling_weight_ne_zero T hunimod eW i (congrArg LinearMap.toContinuousLinearMap h)

end PolycyclicRecognition.CartanWordModel

end

end OAI
