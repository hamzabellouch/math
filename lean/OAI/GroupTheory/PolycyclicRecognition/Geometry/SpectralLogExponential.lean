import OAI.GroupTheory.PolycyclicRecognition.Algebra.SpectralLogValue
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemisimpleExponential
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SpectralConjugation

namespace OAI

/-! # Exponentiating the compatible spectral logarithm -/

noncomputable section
namespace PolycyclicRecognition
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V] [CompleteSpace V]

theorem exp_compatibleSpectralLog (S : Module.End ℂ V) (hS : S.IsSemisimple)
    (hu : IsUnit S) (l : spectralUnitGroup S →* Multiplicative ℂ)
    (m : ℕ) (hl : ∀ z, complexUnitExp (l z) = z.val ^ m) :
    (NormedSpace.exp (LinearMap.toContinuousLinearMap
      (semisimpleSpectralOperator S hS (spectralLogValue S l)))).toLinearMap = S ^ m := by
  rw [exp_semisimpleSpectralOperator]
  apply semisimple_eigenspace_ext S hS
  intro μ x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  have hμ : S.HasEigenvalue μ := Module.End.hasEigenvalue_of_hasEigenvector ⟨hx, hx0⟩
  let z := spectralEigenvalue S hu μ hμ
  have hz : Complex.exp (spectralLogValue S l μ) = μ ^ m := by
    rw [show μ = (z.val : ℂ) from rfl, spectralLogValue_unit]
    exact congrArg Units.val (hl z)
  rw [semisimpleSpectralOperator_apply S hS _ hx, hz]
  exact (Module.End.HasEigenvector.pow_apply ⟨hx, hx0⟩ m).symm

omit [CompleteSpace V] in
theorem compatibleSpectralLog_conjugation (S : Module.End ℂ V) (hS : S.IsSemisimple)
    (l : spectralUnitGroup S →* Multiplicative ℂ)
    (hl : ∀ z, (l (spectralUnitConjugation S z)).toAdd = star (l z).toAdd)
    (c : V →ₗ⋆[ℂ] V) (hc : ∀ x, c (S x) = S (c x)) (x : V) :
    c (semisimpleSpectralOperator S hS (spectralLogValue S l) x) =
      semisimpleSpectralOperator S hS (spectralLogValue S l) (c x) :=
  semisimpleSpectralOperator_conjugation S hS c hc _
    (spectralLogValue_conjugation_all S l hl) x

end PolycyclicRecognition

end

end OAI
