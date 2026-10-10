import OAI.Analysis.Laughlin.FourBody.Levels

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

abbrev RowLevel (t : ℕ) := {T : Fin 16 // t ≤ T.val}

def rowOutputMode (Q t : ℕ) (hQ : 15 ≤ Q) (T : RowLevel t) : Fin (Q+1) :=
  ⟨T.val.val-t,by have h := T.val.isLt; omega⟩

theorem rowOutputMode_injective (Q t : ℕ) (hQ : 15 ≤ Q) :
    Function.Injective (rowOutputMode Q t hQ) := by
  intro T S h
  have he := congrArg Fin.val h
  dsimp [rowOutputMode] at he
  have hT := T.property
  have hS := S.property
  apply Subtype.ext
  apply Fin.ext
  omega

noncomputable def sourceRowSquareVector (Q : ℕ) (hQ : 15 ≤ Q)
    (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (x : Space Q) : Space Q :=
  ((row.2.1 : ℂ)/10^7) • sourcePairEnd Q row.1 x +
    ∑ T : RowLevel row.1, create (rowOutputMode Q row.1 hQ T)
      (sourceRowLevel Q row.1 T.val.val row.2.2 x)

noncomputable def sourceRowFourForm (Q : ℕ) (hQ : 15 ≤ Q)
    (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (x : Space Q) : ℂ :=
  -∑ T : RowLevel row.1, ∑ S : RowLevel row.1,
    occupationInner Q
      (annihilate (rowOutputMode Q row.1 hQ S) (sourceRowLevel Q row.1 T.val.val row.2.2 x))
      (annihilate (rowOutputMode Q row.1 hQ T) (sourceRowLevel Q row.1 S.val.val row.2.2 x))

theorem sourceRowSquareVector_normal (Q : ℕ) (hQ : 15 ≤ Q)
    (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (ht : row.1 ≤ 7) (x : Space Q) :
    (occupationNormSq Q (sourceRowSquareVector Q hQ row x) : ℂ) =
      ((row.2.1 : ℂ)/10^7)^2 * (occupationNormSq Q (sourcePairEnd Q row.1 x) : ℂ) +
      (∑ T : RowLevel row.1, contractionForm Q (sourceThreeEnd Q)
        ((threeBodyLevelMatrix Q row.1 T.val.val row.2.1 row.2.2).map Complex.ofReal) x) +
      sourceRowFourForm Q hQ row x := by
  have h := row_normal_square Q (rowOutputMode Q row.1 hQ)
    (rowOutputMode_injective Q row.1 hQ) ((row.2.1 : ℝ)/10^7)
    (sourcePairEnd Q row.1 x) (fun T => sourceRowLevel Q row.1 T.val.val row.2.2 x)
  have hc : (((row.2.1 : ℝ)/10^7 : ℝ) : ℂ) = (row.2.1 : ℂ)/10^7 := by push_cast; rfl
  rw [hc] at h
  rw [sourceRowSquareVector,h]
  have hl (T : RowLevel row.1) := threeBodyLevelMatrix_Fock Q row.1 T.val.val
    row.2.1 row.2.2 (by omega) (by have hT := T.val.isLt; omega) x
  simp_rw [hl]
  simp only [sourceRowFourForm,rowOutputMode,Finset.sum_add_distrib]
  ring

end Laughlin.Fock

end OAI
