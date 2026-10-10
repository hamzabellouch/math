import OAI.NumberTheory.Ostmann.Arithmetic.HistorySymbolicStep

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicRows
open Characters.RationalHistory HistorySymbolicStep
variable {ι : Type*}

abbrev Row (ι : Type*) := Expr ι × Expr ι

def evalRow (r : Row ι) (x : ι → ℚ) (X Y : ℚ) : ℚ :=
  r.1.rationalEval x * X + r.2.rationalEval x * Y

def pivotRow (s v w : ℤ) (plus minus : Row ι) (u hp hm : List (Expr ι)) : Row ι :=
  (pivot s v w plus.1 minus.1 u hp hm, pivot s v w plus.2 minus.2 u hp hm)

theorem eval_pivotRow (s v w : ℤ) (plus minus : Row ι) (u hp hm : List (Expr ι))
    (x : ι → ℚ) (X Y : ℚ) :
    evalRow (pivotRow s v w plus minus u hp hm) x X Y =
      ((v:ℚ)*(evalRow minus x X Y*(product hm).rationalEval x) -
        (w:ℚ)*(evalRow plus x X Y*(product hp).rationalEval x)) /
      ((s:ℚ)*(product u).rationalEval x) := by
  simp only [evalRow,pivotRow,pivot_eval,div_eq_mul_inv]
  ring

theorem pivot_eval_eq_row (s v w : ℤ) (plus minus : Expr ι)
    (rp rm : Row ι) (u hp hm : List (Expr ι)) (x : ι → ℚ) (X Y : ℚ)
    (hpv : plus.rationalEval x = evalRow rp x X Y)
    (hmv : minus.rationalEval x = evalRow rm x X Y) :
    (pivot s v w plus minus u hp hm).rationalEval x =
      evalRow (pivotRow s v w rp rm u hp hm) x X Y := by
  rw [pivot_eval, hpv, hmv, eval_pivotRow]

def determinant (r t : Row ι) (x : ι → ℚ) : ℚ :=
  r.1.rationalEval x*t.2.rationalEval x-r.2.rationalEval x*t.1.rationalEval x

theorem determinant_plus_pivot (s v w : ℤ) (plus minus : Row ι)
    (u hp hm : List (Expr ι)) (x : ι → ℚ) :
    determinant plus (pivotRow s v w plus minus u hp hm) x =
      ((v:ℚ)*(product hm).rationalEval x /
        ((s:ℚ)*(product u).rationalEval x))*determinant plus minus x := by
  simp only [determinant,pivotRow,pivot_eval,div_eq_mul_inv]
  ring

theorem determinant_pivot_minus (s v w : ℤ) (plus minus : Row ι)
    (u hp hm : List (Expr ι)) (x : ι → ℚ) :
    determinant (pivotRow s v w plus minus u hp hm) minus x =
      (-((w:ℚ)*(product hp).rationalEval x) /
        ((s:ℚ)*(product u).rationalEval x))*determinant plus minus x := by
  simp only [determinant,pivotRow,pivot_eval,div_eq_mul_inv]
  ring

theorem determinant_plus_pivot_ne_zero (s v w : ℤ) (plus minus : Row ι)
    (u hp hm : List (Expr ι)) (x : ι → ℚ)
    (hs : s ≠ 0) (hv : v ≠ 0) (hu : (product u).rationalEval x ≠ 0)
    (hhm : (product hm).rationalEval x ≠ 0) (hd : determinant plus minus x ≠ 0) :
    determinant plus (pivotRow s v w plus minus u hp hm) x ≠ 0 := by
  rw [determinant_plus_pivot]
  exact mul_ne_zero (div_ne_zero (mul_ne_zero (by exact_mod_cast hv) hhm)
    (mul_ne_zero (by exact_mod_cast hs) hu)) hd

theorem determinant_pivot_minus_ne_zero (s v w : ℤ) (plus minus : Row ι)
    (u hp hm : List (Expr ι)) (x : ι → ℚ)
    (hs : s ≠ 0) (hw : w ≠ 0) (hu : (product u).rationalEval x ≠ 0)
    (hhp : (product hp).rationalEval x ≠ 0) (hd : determinant plus minus x ≠ 0) :
    determinant (pivotRow s v w plus minus u hp hm) minus x ≠ 0 := by
  rw [determinant_pivot_minus]
  exact mul_ne_zero (div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (by exact_mod_cast hw) hhp))
    (mul_ne_zero (by exact_mod_cast hs) hu)) hd

end Ostmann.Arithmetic.HistorySymbolicRows

end

end OAI
