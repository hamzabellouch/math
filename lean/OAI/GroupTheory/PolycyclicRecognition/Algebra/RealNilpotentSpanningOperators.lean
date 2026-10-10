import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentSpanningOperators
import Mathlib.Algebra.Lie.BaseChange

namespace OAI

/-! # Real nilpotent representations detected on a spanning set

Complexification allows the weight argument; a real-part retraction reflects
the resulting nilpotence back to the original module.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped TensorProduct

variable {L V : Type*} [LieRing L] [LieAlgebra ℝ L] [LieRing.IsNilpotent L]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule L V] [LieModule ℝ L V]

theorem real_nilpotent_operators_of_spanning_set (S : Set L)
    (hS : Submodule.span ℝ S = ⊤)
    (h : ∀ x ∈ S, IsNilpotent (LieModule.toEnd ℝ L V x)) (x : L) :
    IsNilpotent (LieModule.toEnd ℝ L V x) := by
  let T : Set (ℂ ⊗[ℝ] L) := TensorProduct.mk ℝ ℂ L 1 '' S
  have hT : Submodule.span ℂ T = ⊤ := by
    rw [← Submodule.baseChange_span, hS, Submodule.baseChange_top]
  have hgen (z : ℂ ⊗[ℝ] L) (hz : z ∈ T) :
      IsNilpotent (LieModule.toEnd ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] V) z) := by
    obtain ⟨y, hy, rfl⟩ := hz
    change IsNilpotent (LieModule.toEnd ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] V) (1 ⊗ₜ[ℝ] y))
    rw [LieModule.toEnd_baseChange ℝ ℂ L V y]
    exact (h y hy).map (Module.End.baseChangeHom ℝ ℂ V).toRingHom
  have hn := nilpotent_operators_of_spanning_set T hT hgen (1 ⊗ₜ[ℝ] x)
  rw [LieModule.toEnd_baseChange] at hn
  obtain ⟨k, hk⟩ := hn
  have hz : ((LieModule.toEnd ℝ L V x) ^ k).baseChange ℂ = 0 := by
    rw [LinearMap.baseChange_pow, hk]
  let r : (ℂ ⊗[ℝ] V) →ₗ[ℝ] V :=
    (TensorProduct.lid ℝ V).toLinearMap.comp
      (TensorProduct.map Complex.reLm (LinearMap.id : V →ₗ[ℝ] V))
  refine ⟨k, ?_⟩
  ext v
  have hv := LinearMap.congr_fun hz (1 ⊗ₜ[ℝ] v)
  have hr := congrArg r hv
  simpa [r] using hr

end PolycyclicRecognition

end

end OAI
