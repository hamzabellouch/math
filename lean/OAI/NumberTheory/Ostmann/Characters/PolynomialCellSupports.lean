import OAI.NumberTheory.Ostmann.Characters.PolynomialCellVariation

namespace OAI

/-! # Sharp polynomial support conditions are functions of the root cell -/

namespace Ostmann

open scoped Classical

noncomputable def polynomialSupportCode {I : Type*} (P : I → Polynomial ℝ) (x : ℝ) : I → Bool :=
  fun i => decide (0 ≤ (P i).eval x)

theorem polynomialSupportCode_of_rootCell {I : Type*} (P : I → Polynomial ℝ)
    (S : Finset ℝ) (hroots : ∀ i r, r ∈ (P i).roots → r ∈ S) {x y : ℝ}
    (hxy : rootCellCode S x = rootCellCode S y) :
    polynomialSupportCode P x = polynomialSupportCode P y := by
  funext i
  exact congrArg (fun p : Prop => decide p)
    (propext (polynomial_nonneg_iff_of_root_cell (P i) S (hroots i) hxy))

/-- This is the actual support flag, defined from the inequalities, rather
than an assumption that the supports are regular on the cells. -/
noncomputable def polynomialRootCellFlag {I : Type*} (P : I → Polynomial ℝ)
    (S : Finset ℝ) (keep : (I → Bool) → Bool) (c : S → Ordering) : ℂ :=
  if ∃ x : ℝ, rootCellCode S x = c ∧ keep (polynomialSupportCode P x) = true then 1 else 0

theorem polynomialRootCellFlag_norm {I : Type*} (P : I → Polynomial ℝ)
    (S : Finset ℝ) (keep : (I → Bool) → Bool) (c : S → Ordering) :
    ‖polynomialRootCellFlag P S keep c‖ ≤ 1 := by
  unfold polynomialRootCellFlag
  split_ifs <;> norm_num

theorem polynomialRootCellFlag_value {I : Type*} (P : I → Polynomial ℝ)
    (S : Finset ℝ) (hroots : ∀ i r, r ∈ (P i).roots → r ∈ S)
    (keep : (I → Bool) → Bool) (x : ℝ) :
    polynomialRootCellFlag P S keep (rootCellCode S x) =
      if keep (polynomialSupportCode P x) = true then 1 else 0 := by
  have he : (∃ y : ℝ, rootCellCode S y = rootCellCode S x ∧
      keep (polynomialSupportCode P y) = true) ↔ keep (polynomialSupportCode P x) = true := by
    constructor
    · rintro ⟨y, hy, hk⟩
      rw [polynomialSupportCode_of_rootCell P S hroots hy] at hk
      exact hk
    · intro hk
      exact ⟨x, rfl, hk⟩
  simp only [polynomialRootCellFlag, he]

end Ostmann

end OAI
