import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.CommonDimensions
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators
open MatrixMultiplication.Foundation
open MatrixMultiplication.CommonDimensions

namespace MatrixMultiplication.TerminalProducts

variable {K H : Type*} [CommSemiring K] [Fintype H] [DecidableEq H]

theorem restrict_familyProduct {X Y Z X' Y' Z' : H → Type*}
    [∀ h, Fintype (X h)] [∀ h, Fintype (Y h)] [∀ h, Fintype (Z h)]
    (T : ∀ h, Tensor K (X h) (Y h) (Z h))
    (a : ∀ h, X' h → X h → K) (b : ∀ h, Y' h → Y h → K)
    (c : ∀ h, Z' h → Z h → K) :
    Tensor.restrict (fun x s => ∏ h, a h (x h) (s h))
      (fun y s => ∏ h, b h (y h) (s h)) (fun z s => ∏ h, c h (z h) (s h))
      (familyProduct T) = familyProduct (fun h => Tensor.restrict (a h) (b h) (c h) (T h)) := by
  funext x y z
  simp only [Tensor.restrict, familyProduct, Fintype.prod_sum, ← Finset.prod_mul_distrib]

theorem matrix_restriction_of_history_restrictions {X Y Z : H → Type*}
    [∀ h, Fintype (X h)] [∀ h, Fintype (Y h)] [∀ h, Fintype (Z h)]
    (T : ∀ h, Tensor K (X h) (Y h) (Z h)) (A B C : H → Type*)
    [∀ h, Fintype (A h)] [∀ h, Fintype (B h)] [∀ h, Fintype (C h)]
    [∀ h, DecidableEq (A h)] [∀ h, DecidableEq (B h)] [∀ h, DecidableEq (C h)]
    (a : ∀ h, (A h × B h) → X h → K) (b : ∀ h, (B h × C h) → Y h → K)
    (c : ∀ h, (C h × A h) → Z h → K)
    (hloc : ∀ h, Tensor.restrict (a h) (b h) (c h) (T h) =
      Tensor.matrixCoefficients (A h) (B h) (C h)) :
    ∃ (aa : ((∀ h, A h) × (∀ h, B h)) → (∀ h, X h) → K)
      (bb : ((∀ h, B h) × (∀ h, C h)) → (∀ h, Y h) → K)
      (cc : ((∀ h, C h) × (∀ h, A h)) → (∀ h, Z h) → K),
      Tensor.restrict aa bb cc (familyProduct T) =
        Tensor.matrixCoefficients (∀ h, A h) (∀ h, B h) (∀ h, C h) := by
  classical
  have hp := restrict_familyProduct T a b c
  simp_rw [hloc] at hp
  obtain ⟨aa, bb, cc, hmatrix⟩ := matrix_familyProduct_restrict (K := K) A B C
  refine ⟨Tensor.composeRestrictionMatrix aa (fun x s => ∏ h, a h (x h) (s h)),
    Tensor.composeRestrictionMatrix bb (fun y s => ∏ h, b h (y h) (s h)),
    Tensor.composeRestrictionMatrix cc (fun z s => ∏ h, c h (z h) (s h)), ?_⟩
  rw [← Tensor.restrict_restrict, hp, hmatrix]

end MatrixMultiplication.TerminalProducts

end OAI
