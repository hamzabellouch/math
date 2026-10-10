import OAI.Analysis.KadisonKastler.TracialProjectionInterpolation
import OAI.Analysis.KadisonKastler.MatrixProjectionCuts

namespace OAI

/-! # Bracketing a finite-factor projection by consecutive matrix cuts -/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge
open scoped BigOperators

noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H} [Fintype ι] [DecidableEq ι]

/-- A single unused diagonal slot absorbs the trace remainder between two
consecutive cuts. The conjugating unitary is in the original finite factor. -/
theorem exists_projection_between_matrix_cuts (τ : TracialRepresentation M)
    (hfactor : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M))
    (hdiff : ∀ p : Algebra M, IsStarProjection p → p ≠ 0 →
      ∃ q : Algebra M, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (E : MatrixUnitSystem ι (Algebra M)) (p : AlgebraProjection M)
    (s : Finset ι) (j : ι) (hj : j ∉ s)
    (hlo : (τ.trace (matrixDiagonalCut E s).val).re ≤ (τ.trace p.val).re)
    (hhi : (τ.trace p.val).re ≤ (τ.trace (matrixDiagonalCut E s).val).re +
      (τ.trace (E.entry j j)).re) :
    ∃ (r : AlgebraProjection M) (u : unitary (Algebra M)),
      matrixDiagonalCut E s ≤ r ∧ r ≤ matrixDiagonalCut E (insert j s) ∧
      (u : Algebra M) * r.val * star (u : Algebra M) = p.val := by
  let d : AlgebraProjection M := ⟨E.entry j j, E.diagonal_projection j⟩
  have horth : (matrixDiagonalCut E s).val * d.val = 0 := by
    change (matrixDiagonalCut E s).val * E.entry j j = 0
    rw [matrixDiagonalCut_mul_entry, ite_eq_right hj]
  obtain ⟨r, u, hlo', hhi', hu⟩ := exists_tracial_projection_interpolation τ hfactor hdiff
    p (matrixDiagonalCut E s) d horth hlo hhi
  have he : matrixDiagonalCut E (insert j s) =
      (⟨(matrixDiagonalCut E s).val + d.val,
        (matrixDiagonalCut E s).property.add d.property horth⟩ : AlgebraProjection M) := by
    apply Subtype.ext
    simp only [matrixDiagonalCut, Finset.sum_insert hj]
    exact add_comm _ _
  exact ⟨r, u, hlo', he.symm ▸ hhi', hu⟩

end

end KadisonKastler

end OAI
