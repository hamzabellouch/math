import OAI.Analysis.OperatorAlgebra.ReducedDensityPredual

namespace OAI

/-! Left and right unitary actions on Hilbert–Schmidt vectors. The
conjugation estimate gives the actual left/right intertwining estimate. -/

noncomputable section
open scoped InnerProductSpace TensorProduct

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def hsLeftUnitary (U : H ≃ₗᵢ[ℂ] H) :
    NuclearUltrapower.HilbertSchmidt H ≃ₗᵢ[ℂ] NuclearUltrapower.HilbertSchmidt H :=
  NuclearUltrapower.completionUnitary (E := H ⊗[ℂ] StrongDual ℂ H)
    (F := H ⊗[ℂ] StrongDual ℂ H) (TensorProduct.congrIsometry U
    (LinearIsometryEquiv.refl ℂ (StrongDual ℂ H)))

def hsRightUnitary (U : H ≃ₗᵢ[ℂ] H) :
    NuclearUltrapower.HilbertSchmidt H ≃ₗᵢ[ℂ] NuclearUltrapower.HilbertSchmidt H :=
  NuclearUltrapower.completionUnitary (E := H ⊗[ℂ] StrongDual ℂ H)
    (F := H ⊗[ℂ] StrongDual ℂ H) (TensorProduct.congrIsometry
    (LinearIsometryEquiv.refl ℂ H) (NuclearUltrapower.dualUnitary U.symm))

lemma hsRight_conjugation (U : H ≃ₗᵢ[ℂ] H) (z : NuclearUltrapower.HilbertSchmidt H) :
    hsRightUnitary U (NuclearUltrapower.hsConjugation U z) = hsLeftUnitary U z := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq ((hsRightUnitary U).continuous.comp
        (NuclearUltrapower.hsConjugation U).continuous) (hsLeftUnitary U).continuous
  | ih z =>
      simp only [NuclearUltrapower.hsConjugation_coe, hsRightUnitary, hsLeftUnitary,
        NuclearUltrapower.completionUnitary_coe]
      apply congrArg (fun w : H ⊗[ℂ] StrongDual ℂ H =>
        (w : NuclearUltrapower.HilbertSchmidt H))
      induction z using TensorProduct.inductionOn with
      | tmul x f =>
          obtain ⟨y, rfl⟩ := (InnerProductSpace.toDual ℂ H).surjective f
          simp only [TensorProduct.congrIsometry_apply, TensorProduct.congr_tmul]
          change U x ⊗ₜ[ℂ] NuclearUltrapower.dualUnitary U.symm
            (NuclearUltrapower.dualUnitary U (InnerProductSpace.toDual ℂ H y)) =
              U x ⊗ₜ[ℂ] InnerProductSpace.toDual ℂ H y
          rw [NuclearUltrapower.dualUnitary_toDual, NuclearUltrapower.dualUnitary_toDual,
            U.symm_apply_apply]
      | add z w hz hw => simp only [map_add, hz, hw]

lemma hsLeft_sub_right_norm (U : H ≃ₗᵢ[ℂ] H) (z : NuclearUltrapower.HilbertSchmidt H) :
    ‖hsLeftUnitary U z - hsRightUnitary U z‖ =
      ‖NuclearUltrapower.hsConjugation U z - z‖ := by
  rw [← hsRight_conjugation U z, ← map_sub, (hsRightUnitary U).norm_map]

/-- The square root of a nearly central finite density is an actual
approximate intertwiner for the left and right unitary actions. -/
theorem densityRoot_left_right_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (U : H ≃ₗᵢ[ℂ] H) (z : E ⊗[ℂ] H) :
    ‖hsLeftUnitary U (NuclearUltrapower.densityRoot z) -
      hsRightUnitary U (NuclearUltrapower.densityRoot z)‖ ^ 2 ≤
      ‖finitePredualUnitary U (finiteTensorDensity z) - finiteTensorDensity z‖ := by
  rw [hsLeft_sub_right_norm]
  exact densityRoot_unitary_predual_bound U z

end WeakPureInfiniteness

end

end OAI
