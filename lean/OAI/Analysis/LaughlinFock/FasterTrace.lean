import Mathlib
import OAI.Analysis.LaughlinFock.NumericTrace

namespace OAI

/-! Faster Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def shortNumericRowTerm (D t r s : ℕ) (b c : NumericRowEntry) : ℤ :=
  if D ≤ b.p+b.j+c.i then
    let x := memoIntegerCopyPolynomial D (b.p+b.j+c.i) r b.p b.j c.i
    if x = 0 then 0 else
    let y := memoIntegerCopyPolynomial D (b.p+b.j+c.i) s c.p c.j b.i
    if y = 0 then 0 else
    b.a*c.a * (numericRowFactor D t b c : ℤ) * x * y
  else 0

theorem numericRowTerm_short (D t r s : ℕ) (b c : NumericRowEntry) :
    numericRowTerm D t r s b c = shortNumericRowTerm D t r s b c := by
  unfold numericRowTerm shortNumericRowTerm
  dsimp only
  split_ifs <;> simp_all

def directIntegerSum {α : Type*} (f : α → ℤ) : List α → ℤ
  | [] => 0
  | a::as => f a + directIntegerSum f as

theorem directIntegerSum_spec {α : Type*} (f : α → ℤ) (ls : List α) :
    (ls.map f).sum = directIntegerSum f ls := by
  induction ls with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, List.sum_cons, directIntegerSum, ih]

def shortNumericFourTrace (D : ℕ) (t : Fin 8) (r s : ℕ) : ℤ :=
  -(directIntegerSum (fun b => directIntegerSum (shortNumericRowTerm D t.val r s b)
    (numericRowData t)) (numericRowData t))

theorem numericFourTrace_short (D : ℕ) (t : Fin 8) (r s : ℕ) :
    numericFourTrace D t r s = shortNumericFourTrace D t r s := by
  simp only [numericFourTrace, shortNumericFourTrace, numericRowTerm_short, directIntegerSum_spec]

def shortNumericRowsFourTrace (D r s : ℕ) : ℤ :=
  shortNumericFourTrace D 0 r s + shortNumericFourTrace D 1 r s +
  shortNumericFourTrace D 2 r s + shortNumericFourTrace D 3 r s +
  shortNumericFourTrace D 4 r s + shortNumericFourTrace D 5 r s +
  shortNumericFourTrace D 6 r s + shortNumericFourTrace D 7 r s

theorem integerRowsFourTrace_short {D : ℕ} (hD : D ≤ 23) (r s : CopyLabel D) :
    integerRowsFourTrace D r s = (shortNumericRowsFourTrace D r.val.val s.val.val : ℚ) / fourCommonDenominator := by
  rw [integerRowsFourTrace_numeric hD]
  simp only [numericRowsFourTrace, numericFourTrace_short, Fin.sum_univ_succ]
  simp only [shortNumericRowsFourTrace]
  congr 2
  simp only [Fin.isValue, Fin.succ_zero_eq_one]
  abel

end LaughlinFock
end

end OAI
