import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialChartCoordinates

namespace OAI

/-! # Exact height scaling in nilpotent word charts -/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

/-- A linear height that kills brackets scales exactly in the word-length
chart. This is independent of a choice of graded limit: all nontrivial
bracket words have zero height, while each letter has weight one. -/
theorem word_length_chart_height
    {I L W : Type*} [Fintype I] [DecidableEq I]
    [LieRing L] [LieAlgebra ℝ L] [AddCommGroup W] [Module ℝ W]
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (h : L →ₗ[ℝ] W) (hbracket : ∀ x y : L, h ⁅x, y⁆ = 0)
    {r : ℝ} (hr : 0 < r) (z : Fin (finrank ℝ L) → ℝ) :
    h ((exponentialRescaleBasis (WordBasisSelections.basis X S β)
      (fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)) (Real.log r)).equivFun.symm z) =
      r • h ((WordBasisSelections.basis X S β).equivFun.symm z) := by
  let b := WordBasisSelections.basis X S β
  let br := exponentialRescaleBasis b
    (fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)) (Real.log r)
  have hb (j : Fin (finrank ℝ L)) : h (br j) = r • h (b j) := by
    simp only [br, exponentialRescaleBasis, Basis.unitsSMul_apply,
      Units.smul_def, Units.val_mk0, map_smul]
    have he := WordBasisSelections.eval_words X S β j
    change evalBracketWord X (β.val j) = b j at he
    rw [← he]
    cases hw : (β.val j : FreeMagma I) with
    | of i => simp only [bracketWordLength, Nat.cast_one, mul_one, Real.exp_log hr]
    | mul u v =>
        change Real.exp (Real.log r * (bracketWordLength (u * v) : ℝ)) •
          h ⁅evalBracketWord X u, evalBracketWord X v⁆ =
            r • h ⁅evalBracketWord X u, evalBracketWord X v⁆
        rw [hbracket, smul_zero, smul_zero]
  change h (br.equivFun.symm z) = r • h (b.equivFun.symm z)
  rw [Basis.equivFun_symm_apply, map_sum, Basis.equivFun_symm_apply, map_sum,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, map_smul, hb, smul_comm]

end PolycyclicRecognition

end

end OAI
