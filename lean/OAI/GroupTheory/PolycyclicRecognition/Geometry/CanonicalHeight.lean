import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.Basic.Real.Basic

namespace OAI

/-! # The linear canonical height quotient

The height space is the quotient by the common kernel of the diagonal adjoint
characters. The induced characters on this quotient separate points.
-/

namespace PolycyclicRecognition

open scoped BigOperators

section Linear

variable {L I : Type*} [AddCommGroup L] [Module ℝ L]

/-- The common kernel of the diagonal characters. Empty families give `⊤`. -/
def heightKernel (χ : I → L →ₗ[ℝ] ℝ) : Submodule ℝ L := ⨅ i, (χ i).ker

/-- The canonical linear height space. -/
abbrev HeightSpace (χ : I → L →ₗ[ℝ] ℝ) := L ⧸ heightKernel χ

/-- The quotient map defining infinitesimal height. -/
def heightProjection (χ : I → L →ₗ[ℝ] ℝ) : L →ₗ[ℝ] HeightSpace χ :=
  (heightKernel χ).mkQ

/-- Each character descends to the height quotient. -/
def heightCharacter (χ : I → L →ₗ[ℝ] ℝ) (i : I) : HeightSpace χ →ₗ[ℝ] ℝ :=
  (heightKernel χ).liftQ (χ i) (iInf_le _ i)

@[simp] theorem heightCharacter_projection (χ : I → L →ₗ[ℝ] ℝ) (i : I) (x : L) :
    heightCharacter χ i (heightProjection χ x) = χ i x := rfl

theorem heightProjection_surjective (χ : I → L →ₗ[ℝ] ℝ) :
    Function.Surjective (heightProjection χ) := (heightKernel χ).mkQ_surjective

@[simp] theorem mem_heightKernel (χ : I → L →ₗ[ℝ] ℝ) (x : L) :
    x ∈ heightKernel χ ↔ ∀ i, χ i x = 0 := by
  simp only [heightKernel, Submodule.mem_iInf, LinearMap.mem_ker]

/-- The common kernel has been removed: all induced character values vanish
only at the zero height. -/
theorem heightCharacters_separate (χ : I → L →ₗ[ℝ] ℝ) (w : HeightSpace χ)
    (hw : ∀ i, heightCharacter χ i w = 0) : w = 0 := by
  obtain ⟨x, rfl⟩ := heightProjection_surjective χ w
  apply (Submodule.Quotient.mk_eq_zero (heightKernel χ)).mpr
  exact (mem_heightKernel χ x).mpr hw

/-- A relation among the original characters descends without changing its
coefficients. This is used with the trace-zero, positive-multiplicity relation. -/
theorem heightCharacter_relation [Fintype I]
    (χ : I → L →ₗ[ℝ] ℝ) (c : I → ℝ)
    (h : ∀ x : L, ∑ i, c i * χ i x = 0) (w : HeightSpace χ) :
    ∑ i, c i * heightCharacter χ i w = 0 := by
  obtain ⟨x, rfl⟩ := heightProjection_surjective χ w
  exact h x

/-- Vanishing diagonal characters give a zero-dimensional height quotient. -/
theorem heightSpace_subsingleton_of_characters_zero
    (χ : I → L →ₗ[ℝ] ℝ) (hχ : ∀ i, χ i = 0) : Subsingleton (HeightSpace χ) := by
  have hz (w : HeightSpace χ) : w = 0 := by
    apply heightCharacters_separate χ
    obtain ⟨x, rfl⟩ := heightProjection_surjective χ w
    intro i
    simp [hχ i]
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- Conversely, a trivial height quotient forces all the diagonal characters
to vanish. -/
theorem characters_zero_of_heightSpace_subsingleton
    (χ : I → L →ₗ[ℝ] ℝ) [Subsingleton (HeightSpace χ)] : ∀ i, χ i = 0 := by
  intro i
  ext x
  rw [← heightCharacter_projection χ i x, Subsingleton.elim (heightProjection χ x) 0]
  exact map_zero _

end Linear

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- Characters vanishing on brackets make every bracket have zero height. -/
theorem heightProjection_lie_eq_zero
    (χ : I → L →ₗ[ℝ] ℝ) (hχ : ∀ i (x y : L), χ i ⁅x, y⁆ = 0) (x y : L) :
    heightProjection χ ⁅x, y⁆ = 0 := by
  apply (Submodule.Quotient.mk_eq_zero (heightKernel χ)).mpr
  exact (mem_heightKernel χ ⁅x, y⁆).mpr fun i => hχ i x y

end PolycyclicRecognition

end OAI
