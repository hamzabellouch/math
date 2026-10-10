import OAI.Analysis.IrrationalRotation.Analysis.ConcretePredualCore
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.DoubleDual

namespace OAI

noncomputable section
namespace Invariant233.ConcretePredual

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

@[simp] theorem vectorFunctional_add_left (M : VonNeumannAlgebra H) (x z y : H) :
    vectorFunctional M (x + z) y = vectorFunctional M x y + vectorFunctional M z y := by
  ext A
  simp

@[simp] theorem vectorFunctional_add_right (M : VonNeumannAlgebra H) (x y z : H) :
    vectorFunctional M x (y + z) = vectorFunctional M x y + vectorFunctional M x z := by
  ext A
  simp

@[simp] theorem vectorFunctional_smul_left (M : VonNeumannAlgebra H) (c : ℂ) (x y : H) :
    vectorFunctional M (c • x) y = star c • vectorFunctional M x y := by
  ext A
  simp [mul_comm]

@[simp] theorem vectorFunctional_smul_right (M : VonNeumannAlgebra H) (c : ℂ) (x y : H) :
    vectorFunctional M x (c • y) = c • vectorFunctional M x y := by
  ext A
  simp

theorem norm_vectorFunctional_le (M : VonNeumannAlgebra H) (x y : H) :
    ‖vectorFunctional M x y‖ ≤ ‖x‖ * ‖y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro A
  calc
    ‖vectorFunctional M x y A‖ ≤ ‖x‖ * ‖(A : H →L[ℂ] H) y‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖A‖ * ‖y‖) :=
      mul_le_mul_of_nonneg_left ((A : H →L[ℂ] H).le_opNorm y) (norm_nonneg _)
    _ = (‖x‖ * ‖y‖) * ‖A‖ := by ring

def representingForm (M : VonNeumannAlgebra H)
    (Φ : StrongDual ℂ (StrongDual ℂ M)) : H →L⋆[ℂ] H →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    { toFun := fun x =>
        { toFun := fun y => Φ (vectorFunctional M x y)
          map_add' := by intro y z; simp
          map_smul' := by intro c y; simp }
      map_add' := by intro x z; ext y; simp
      map_smul' := by intro c x; ext y; simp } ‖Φ‖
    (by
      intro x y
      exact (Φ.le_opNorm _).trans (by
        calc
          ‖Φ‖ * ‖vectorFunctional M x y‖ ≤ ‖Φ‖ * (‖x‖ * ‖y‖) :=
            mul_le_mul_of_nonneg_left (norm_vectorFunctional_le M x y) (norm_nonneg Φ)
          _ = ‖Φ‖ * ‖x‖ * ‖y‖ := by ring))

def representingOperator (M : VonNeumannAlgebra H)
    (Φ : StrongDual ℂ (StrongDual ℂ M)) : H →L[ℂ] H :=
  (InnerProductSpace.continuousLinearMapOfBilin (representingForm M Φ)).adjoint

@[simp] theorem inner_representingOperator (M : VonNeumannAlgebra H)
    (Φ : StrongDual ℂ (StrongDual ℂ M)) (x y : H) :
    inner ℂ x (representingOperator M Φ y) = Φ (vectorFunctional M x y) := by
  rw [representingOperator, ContinuousLinearMap.adjoint_inner_right,
    InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

theorem representingOperator_mem (M : VonNeumannAlgebra H)
    (Φ : StrongDual ℂ (StrongDual ℂ M)) : representingOperator M Φ ∈ M := by
  have hmem : representingOperator M Φ ∈ M.commutant.commutant := by
    rw [VonNeumannAlgebra.mem_commutant_iff]
    intro B hB
    ext y
    apply ext_inner_left ℂ
    intro x
    change inner ℂ x (B (representingOperator M Φ y)) =
      inner ℂ x (representingOperator M Φ (B y))
    rw [← ContinuousLinearMap.adjoint_inner_left B (representingOperator M Φ y) x,
      inner_representingOperator, inner_representingOperator]
    congr 1
    ext A
    rw [vectorFunctional_apply, vectorFunctional_apply,
      ContinuousLinearMap.adjoint_inner_left]
    congr 1
    exact congrArg (fun Q : H →L[ℂ] H => Q y)
      ((VonNeumannAlgebra.mem_commutant_iff.mp hB) A A.property).symm
  simpa only [M.commutant_commutant] using hmem

theorem evaluation_surjective (M : VonNeumannAlgebra H) :
    Function.Surjective (evaluation M) := by
  intro ℓ
  obtain ⟨Φ, hΦ, _hΦnorm⟩ := exists_extension_norm_eq (predual M) ℓ
  let A : M := ⟨representingOperator M Φ, representingOperator_mem M Φ⟩
  let Ψ : StrongDual ℂ (StrongDual ℂ M) :=
    Φ - NormedSpace.inclusionInDoubleDual ℂ M A
  have hker : predual M ≤ Ψ.ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro f ⟨⟨x, y⟩, rfl⟩
      change Φ (vectorFunctional M x y) - (vectorFunctional M x y) A = 0
      rw [vectorFunctional_apply]
      change Φ (vectorFunctional M x y) - inner ℂ x (representingOperator M Φ y) = 0
      simp
    · exact Ψ.isClosed_ker
  refine ⟨A, ?_⟩
  ext f
  have hf := hker f.property
  change Φ (f : StrongDual ℂ M) - (f : StrongDual ℂ M) A = 0 at hf
  rw [evaluation_apply, ← sub_eq_zero.mp hf]
  exact hΦ f

end Invariant233.ConcretePredual

end

end OAI
