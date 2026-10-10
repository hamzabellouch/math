import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemisimpleExponential
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ComplexSquareLogarithm

namespace OAI

/-! # The logarithm of the square of a semisimple complex operator -/

noncomputable section
namespace PolycyclicRecognition

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V] [CompleteSpace V]

def semisimpleSquareLog (S : Module.End ℂ V) (hS : S.IsSemisimple) : Module.End ℂ V :=
  semisimpleSpectralOperator S hS complexSquareLog

theorem exp_semisimpleSquareLog (S : Module.End ℂ V) (hS : S.IsSemisimple)
    (hu : IsUnit S) :
    (NormedSpace.exp (LinearMap.toContinuousLinearMap
      (semisimpleSquareLog S hS))).toLinearMap = S ^ 2 := by
  rw [semisimpleSquareLog, exp_semisimpleSpectralOperator]
  apply semisimple_eigenspace_ext S hS
  intro μ x hx
  by_cases hμ : μ = 0
  · have hz : S x = 0 := by simpa [hμ] using Module.End.mem_eigenspace_iff.mp hx
    have hi : Function.Injective S := by
      obtain ⟨u, rfl⟩ := hu
      intro a b hab
      have := congrArg (fun z => ((u⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) z) hab
      simpa only [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply] using this
    have hx0 : x = 0 := hi (hz.trans (map_zero S).symm)
    simp [hx0]
  · rw [semisimpleSpectralOperator_apply S hS _ hx, exp_complexSquareLog hμ]
    change μ ^ 2 • x = S (S x)
    rw [Module.End.mem_eigenspace_iff.mp hx, map_smul,
      Module.End.mem_eigenspace_iff.mp hx, smul_smul, pow_two]

end PolycyclicRecognition

end

end OAI
