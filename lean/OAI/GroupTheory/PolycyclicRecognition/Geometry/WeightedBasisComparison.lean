import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordBoxComparison

namespace OAI

/-! # Comparing any selected word box with a maximizing word box -/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped BigOperators

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

omit [FiniteDimensional ℝ L] in
/-- A fixed constant controls every selected word basis in every maximizing
basis, at all nonnegative scales. Thus a varying basis in a sampling row
can be replaced by the fixed maximizing basis without an exponential loss. -/
theorem exists_uniform_rescaled_basis_comparison
    (X : I → L) (S : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (cost : S → ℝ) (β γ : WordBasisSelections X S),
      IsMaximizingColumnBasis (wordListCoordinates X S b₀) cost β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ x : L,
        ‖(exponentialRescaleBasis (WordBasisSelections.basis X S β)
          (fun j => cost (β.val j)) r).equivFun x‖ ≤
        C * ‖(exponentialRescaleBasis (WordBasisSelections.basis X S γ)
          (fun j => cost (γ.val j)) r).equivFun x‖ := by
  obtain ⟨D, hD, hcompare⟩ := exists_word_box_comparison_constant X S b₀
  refine ⟨1 + D, by linarith, ?_⟩
  intro cost β γ hβ r hr x
  have h := hcompare cost cost β γ hβ hr (ε := 0) (by intro w; simp) x
  simp only [zero_mul, Real.exp_zero, mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

end PolycyclicRecognition

end

end OAI
