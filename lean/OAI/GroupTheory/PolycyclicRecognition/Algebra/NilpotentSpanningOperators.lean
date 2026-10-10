import Mathlib.Algebra.Lie.Weights.Linear
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace OAI

/-! # Nilpotent operators spanning a complex nilpotent Lie algebra

Every weight vanishes on the spanning set, hence on the entire Lie algebra.
The zero weight space is therefore the whole representation.
-/

noncomputable section
namespace PolycyclicRecognition

variable {L V : Type*} [LieRing L] [LieAlgebra ℂ L] [LieRing.IsNilpotent L]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [LieRingModule L V] [LieModule ℂ L V]

theorem nilpotent_operators_of_spanning_set (S : Set L)
    (hS : Submodule.span ℂ S = ⊤)
    (h : ∀ x ∈ S, IsNilpotent (LieModule.toEnd ℂ L V x)) (x : L) :
    IsNilpotent (LieModule.toEnd ℂ L V x) := by
  have hweight (χ : LieModule.Weight ℂ L V) : (χ : L → ℂ) = 0 := by
    funext y
    change χ y = 0
    have hy : y ∈ Submodule.span ℂ S := by rw [hS]; trivial
    induction hy using Submodule.span_induction with
    | mem y hy => exact χ.apply_eq_zero_of_isNilpotent y (h y hy)
    | zero => exact map_zero (χ.toLinear ℂ L V)
    | add y z _ _ hy hz =>
        change χ (y + z) = 0
        rw [map_add, hy, hz, add_zero]
    | smul a y _ hy =>
        change χ (a • y) = 0
        rw [map_smul, hy, smul_zero]
  have htop : LieModule.genWeightSpace V (0 : L → ℂ) = ⊤ := by
    apply le_antisymm le_top
    rw [← LieModule.iSup_genWeightSpace_eq_top' ℂ L V]
    apply iSup_le
    intro χ
    rw [hweight χ]
  obtain ⟨k, hk⟩ := LieModule.exists_genWeightSpace_zero_le_ker_of_isNoetherian ℂ V x
  refine ⟨k, ?_⟩
  ext v
  exact hk (by rw [htop]; trivial)

end PolycyclicRecognition

end

end OAI
