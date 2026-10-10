import Mathlib
import OAI.Analysis.LaughlinFock.FasterTrace

namespace OAI

/-! Sparse Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 
structure CollectedFourTerm where
  p : ℕ
  j : ℕ
  k : ℕ
  q : ℕ
  l : ℕ
  i : ℕ
  a : ℤ
  deriving DecidableEq

def collectFourTerm (D t : ℕ) (b c : NumericRowEntry) : CollectedFourTerm :=
  ⟨b.p,b.j,c.i,c.p,c.j,b.i,b.a*c.a*(numericRowFactor D t b c : ℤ)⟩

def collectedTermValue (D r s : ℕ) (a : CollectedFourTerm) : ℤ :=
  let x := memoIntegerCopyPolynomial D (a.p+a.j+a.k) r a.p a.j a.k
  if x=0 then 0 else
  let y := memoIntegerCopyPolynomial D (a.p+a.j+a.k) s a.q a.l a.i
  if y=0 then 0 else a.a*x*y

theorem collectedTermValue_spec (D t r s : ℕ) (b c : NumericRowEntry) :
    collectedTermValue D r s (collectFourTerm D t b c) =
      b.a*c.a*(numericRowFactor D t b c : ℤ)*
        memoIntegerCopyPolynomial D (b.p+b.j+c.i) r b.p b.j c.i *
        memoIntegerCopyPolynomial D (b.p+b.j+c.i) s c.p c.j b.i := by
  unfold collectedTermValue collectFourTerm
  dsimp only
  split_ifs <;> simp_all

def collectNumericRow (D : ℕ) (t : Fin 8) : List CollectedFourTerm :=
  (numericRowData t).flatMap fun b => (numericRowData t).flatMap fun c =>
    if D ≤ b.p+b.j+c.i then [collectFourTerm D t.val b c] else []

theorem list_flatMap_sum_int {α : Type*} (xs : List α) (f : α → List ℤ) :
    (xs.flatMap f).sum = (xs.map (fun a => (f a).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons, ih]

theorem collectNumericRow_sum (D : ℕ) (t : Fin 8) (r s : ℕ) :
    numericFourTrace D t r s =
      -(((collectNumericRow D t).map (collectedTermValue D r s)).sum) := by
  unfold numericFourTrace collectNumericRow
  simp only [List.map_flatMap, list_flatMap_sum_int]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  apply congrArg List.sum
  apply List.map_congr_left
  intro c hc
  unfold numericRowTerm
  split_ifs
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      collectedTermValue_spec]
  · rfl

def collectedFourTerms (D : ℕ) : List CollectedFourTerm :=
  collectNumericRow D 0 ++ collectNumericRow D 1 ++ collectNumericRow D 2 ++
  collectNumericRow D 3 ++ collectNumericRow D 4 ++ collectNumericRow D 5 ++
  collectNumericRow D 6 ++ collectNumericRow D 7

def collectedFourTrace (D r s : ℕ) (ls : List CollectedFourTerm) : ℤ :=
  -(directIntegerSum (collectedTermValue D r s) ls)

theorem numericRowsFourTrace_collected (D r s : ℕ) :
    numericRowsFourTrace D r s = collectedFourTrace D r s (collectedFourTerms D) := by
  simp only [numericRowsFourTrace, collectNumericRow_sum, Fin.sum_univ_succ,
    collectedFourTrace, collectedFourTerms, ← directIntegerSum_spec,
    List.map_append, List.sum_append]
  simp only [Fin.isValue, Fin.succ_zero_eq_one]
  abel

theorem integerRowsFourTrace_collected {D : ℕ} (hD : D ≤ 23) (ls : List CollectedFourTerm)
    (hls : collectedFourTerms D = ls) (r s : CopyLabel D) :
    integerRowsFourTrace D r s =
      (collectedFourTrace D r.val.val s.val.val ls : ℚ) / fourCommonDenominator := by
  rw [integerRowsFourTrace_numeric hD, numericRowsFourTrace_collected, hls]

end LaughlinFock
end

end OAI
