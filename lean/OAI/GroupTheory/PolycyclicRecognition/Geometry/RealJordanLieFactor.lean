import OAI.GroupTheory.PolycyclicRecognition.Geometry.JordanLieFactor
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexifiedLieAutomorphism

namespace OAI

/-! # The real semisimple Jordan factor preserves the Lie bracket -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

theorem real_semisimple_jordan_factor_map_lie (A : L ≃ₗ⁅ℝ⁆ L) (S : Module.End ℝ L)
    (hS : S.IsSemisimple) (hc : Commute A.toLinearMap S)
    (hn : IsNilpotent (A.toLinearMap - S)) (x y : L) :
    S ⁅x, y⁆ = ⁅S x, S y⁆ := by
  let f := Module.End.baseChangeHom ℝ ℂ L
  have hc' : Commute (complexifiedLieEquiv L A).toLinearMap (S.baseChange ℂ) := hc.map f
  let CA : Module.End ℂ (ℂ ⊗[ℝ] L) := (complexifiedLieEquiv L A).toLinearMap
  let CS : Module.End ℂ (ℂ ⊗[ℝ] L) := S.baseChange ℂ
  have hn' : IsNilpotent (CA - CS) := by
    obtain ⟨k, hk⟩ := hn
    refine ⟨k, ?_⟩
    change (f A.toLinearMap - f S) ^ k = 0
    rw [← map_sub, ← map_pow, hk, map_zero]
  have h := semisimple_jordan_factor_map_lie (complexifiedLieEquiv L A).toLieHom
    (S.baseChange ℂ) (complexifiedEnd_semisimple L S hS) hc' hn'
    ((1 : ℂ) ⊗ₜ[ℝ] x) ((1 : ℂ) ⊗ₜ[ℝ] y)
  apply complexificationLieHom_injective L
  change (1 : ℂ) ⊗ₜ[ℝ] S ⁅x, y⁆ = (1 : ℂ) ⊗ₜ[ℝ] ⁅S x, S y⁆
  simpa using h

end PolycyclicRecognition

end

end OAI
