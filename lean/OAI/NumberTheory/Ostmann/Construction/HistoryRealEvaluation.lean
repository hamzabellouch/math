import OAI.NumberTheory.Ostmann.Arithmetic.MovingRealResidues

namespace OAI

/-! # Real evaluation of the original cleared history formulas -/

namespace Ostmann.HistoryFormula
open scoped Classical BigOperators

@[simp] theorem realEval_prime {σ : Type*} (i : σ) (x : σ → ℝ) :
    (prime i).realEval x = x i := by
  simp only [realEval, cleared, ClearedHistoryValue.ofVariable, MvPolynomial.eval₂_X,
    Int.cast_one, div_one]

@[simp] theorem realEval_external {σ : Type*} (a : ℤ) (x : σ → ℝ) :
    (external a).realEval x = a := by
  simp only [realEval, cleared, ClearedHistoryValue.constant, MvPolynomial.eval₂_C,
    Int.coe_castRingHom, Int.cast_one, div_one]

@[simp] theorem realEval_product {σ : Type*} (l r : HistoryFormula σ) (x : σ → ℝ) :
    (product l r).realEval x = l.realEval x * r.realEval x := by
  simp only [realEval, cleared, ClearedHistoryValue.prod, Fintype.prod_bool,
    Bool.false_eq_true, ite_false, ite_true, MvPolynomial.eval₂_mul, Int.cast_mul]
  ring

@[simp] theorem realEval_solve {σ : Type*} (l r : HistoryFormula σ) (v w s : ℤ)
    (hs : s ≠ 0) (x : σ → ℝ) :
    (solve l r v w s hs).realEval x = (v * r.realEval x - w * l.realEval x) / s := by
  have hL : (l.cleared.denominator : ℝ) ≠ 0 := Int.cast_ne_zero.mpr l.cleared.denominator_ne_zero
  have hR : (r.cleared.denominator : ℝ) ≠ 0 := Int.cast_ne_zero.mpr r.cleared.denominator_ne_zero
  have hS : (s : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hs
  simp only [realEval, cleared, ClearedHistoryValue.pivot, MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, Int.coe_castRingHom, Int.cast_mul]
  field_simp

theorem realEval_bind {σ τ : Type*} (F : HistoryFormula σ) (f : σ → HistoryFormula τ)
    (x : τ → ℝ) : (F.bind f).realEval x = F.realEval (fun i => (f i).realEval x) := by
  induction F with
  | prime i => simp only [bind, realEval_prime]
  | external z => simp only [bind, realEval_external]
  | product l r hl hr => simp only [bind, realEval_product, hl, hr]
  | solve l r v w s hs hl hr => simp only [bind, realEval_solve, hl, hr]

theorem realEval_listProduct {σ : Type*} (fs : List (HistoryFormula σ)) (x : σ → ℝ) :
    (listProduct fs).realEval x = (fs.map (fun F => F.realEval x)).prod := by
  induction fs with
  | nil => simp [listProduct]
  | cons f fs ih => simp only [listProduct, realEval_product, List.map_cons, List.prod_cons, ih]

end Ostmann.HistoryFormula

end OAI
