import OAI.NumberTheory.Ostmann.Characters.TemplateLeafSymbolic
import OAI.NumberTheory.Ostmann.Characters.ZeroVariable

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
open SymbolicHistory
variable {ι : Type*} [DecidableEq ι]

private theorem cleared_setZero_ne_zero (e : Expr ι) (a : ι → ℤ)
    (i : ι) (p : ℕ) (hp : p.Prime) (hi : a i=(p:ℤ))
    (hclear : e.denominator*e.integerEval a=MvPolynomial.eval a e.numerator)
    (hden : IsCoprime (p:ℤ) e.denominator) (hcop : IsCoprime (p:ℤ) (e.integerEval a)) :
    ZeroVariable.setZero i e.numerator ≠ 0 := by
  intro hz
  have hd := ZeroVariable.prime_dvd_reconstructed_of_setZero_eq_zero i e.numerator hz a p hi
    e.denominator (e.integerEval a) hclear hden
  have hu : IsUnit (p:ℤ) := hcop.isUnit_of_dvd hd
  have hh : (p:ℤ)=1 ∨ (p:ℤ)= -1 := Int.isUnit_iff.mp hu
  have hp2 : (2:ℤ)≤p := by exact_mod_cast hp.two_le
  omega

theorem pivot_setZero_ne_zero (k : ℕ) (B V : (j:ℕ) → State k (j+1) → ℤ) (j : ℕ)
    (s : ℤ) (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) (a : ι → ℤ)
    (he : ∀ i, HistoryReconstruction.Good a (e i))
    (h : Supported k B V j s (evalExpressions a e) t)
    (q : Expr ι) (hq : q ∈ pivotExpressions k j s e t)
    (i : ι) (p : ℕ) (hp : p.Prime) (hi : a i=(p:ℤ))
    (hden : IsCoprime (p:ℤ) q.denominator) (hcop : IsCoprime (p:ℤ) (q.integerEval a)) :
    ZeroVariable.setZero i q.numerator ≠ 0 :=
  cleared_setZero_ne_zero q a i p hp hi (pivot_cleared k B V j s e t a he h q hq).2 hden hcop

theorem bottom_period_setZero_ne_zero (k : ℕ) (B V : (j:ℕ) → State k (j+1) → ℤ) (j : ℕ)
    (b : Bool) (s : ℤ) (e : Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j) (a : ι → ℤ)
    (he : ∀ i, HistoryReconstruction.Good a (e i))
    (h : Supported k B V j s (evalExpressions a e) t)
    (q : BottomExpression (ι:=ι) k) (hq : q ∈ bottomExpressions k j b s e t)
    (i : ι) (p : ℕ) (hp : p.Prime) (hi : a i=(p:ℤ))
    (hden : IsCoprime (p:ℤ) (periodExpression k q.2.2).denominator)
    (hcop : IsCoprime (p:ℤ) (period k 0 (evalExpressions a q.2.2))) :
    ZeroVariable.setZero i (periodExpression k q.2.2).numerator ≠ 0 := by
  apply cleared_setZero_ne_zero (periodExpression k q.2.2) a i p hp hi
  · simpa only [periodExpression_eval] using (bottom_period_cleared k B V j b s e t a he h q hq).2
  · exact hden
  · simpa only [periodExpression_eval] using hcop

end Ostmann.Characters.Template

end

end OAI
