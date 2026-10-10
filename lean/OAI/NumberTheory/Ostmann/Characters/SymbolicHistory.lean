import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Characters.SymbolicHistory
open MvPolynomial

inductive Expr (ι:Type*)
  | atom (i:ι)
  | fixed (c:ℤ)
  | add (a b:Expr ι)
  | sub (a b:Expr ι)
  | mul (a b:Expr ι)
  | divide (a:Expr ι) (d:ℤ)

namespace Expr
variable {ι:Type*}

private theorem rational_castHom_apply (c:ℤ) : (Int.castRingHom ℚ) c=(c:ℚ) := rfl

def denominator : Expr ι→ℤ
  | .atom _ => 1
  | .fixed _ => 1
  | .add a b => a.denominator*b.denominator
  | .sub a b => a.denominator*b.denominator
  | .mul a b => a.denominator*b.denominator
  | .divide a d => a.denominator*d

def numerator : Expr ι→MvPolynomial ι ℤ
  | .atom i => X i
  | .fixed c => C c
  | .add a b => a.numerator*C b.denominator+b.numerator*C a.denominator
  | .sub a b => a.numerator*C b.denominator-b.numerator*C a.denominator
  | .mul a b => a.numerator*b.numerator
  | .divide a _ => a.numerator

def Valid : Expr ι→Prop
  | .atom _ => True
  | .fixed _ => True
  | .add a b => a.Valid ∧ b.Valid
  | .sub a b => a.Valid ∧ b.Valid
  | .mul a b => a.Valid ∧ b.Valid
  | .divide a d => a.Valid ∧ d≠0

def rationalEval (x:ι→ℚ) : Expr ι→ℚ
  | .atom i => x i
  | .fixed c => c
  | .add a b => a.rationalEval x+b.rationalEval x
  | .sub a b => a.rationalEval x-b.rationalEval x
  | .mul a b => a.rationalEval x*b.rationalEval x
  | .divide a d => a.rationalEval x/(d:ℚ)

def integerEval (x:ι→ℤ) : Expr ι→ℤ
  | .atom i => x i
  | .fixed c => c
  | .add a b => a.integerEval x+b.integerEval x
  | .sub a b => a.integerEval x-b.integerEval x
  | .mul a b => a.integerEval x*b.integerEval x
  | .divide a d => a.integerEval x/d

def IntegralAt (x:ι→ℤ) : Expr ι→Prop
  | .atom _ => True
  | .fixed _ => True
  | .add a b => a.IntegralAt x ∧ b.IntegralAt x
  | .sub a b => a.IntegralAt x ∧ b.IntegralAt x
  | .mul a b => a.IntegralAt x ∧ b.IntegralAt x
  | .divide a d => a.IntegralAt x ∧ d∣a.integerEval x

theorem denominator_ne_zero (e:Expr ι) (h:e.Valid) : e.denominator≠0 := by
  induction e with
  | atom i => exact one_ne_zero
  | fixed c => exact one_ne_zero
  | add a b ia ib => exact mul_ne_zero (ia h.1) (ib h.2)
  | sub a b ia ib => exact mul_ne_zero (ia h.1) (ib h.2)
  | mul a b ia ib => exact mul_ne_zero (ia h.1) (ib h.2)
  | divide a d ia => exact mul_ne_zero (ia h.1) h.2

theorem rationalEval_eq (e:Expr ι) (h:e.Valid) (x:ι→ℚ) :
    e.rationalEval x=eval₂ (Int.castRingHom ℚ) x e.numerator/(e.denominator:ℚ) := by
  induction e with
  | atom i => simp [rationalEval,numerator,denominator]
  | fixed c =>
    simp only [rationalEval,numerator,denominator,eval₂_C,Int.cast_one,div_one]
    rfl
  | add a b ia ib =>
    have ha : (a.denominator:ℚ)≠0 := by exact_mod_cast a.denominator_ne_zero h.1
    have hb : (b.denominator:ℚ)≠0 := by exact_mod_cast b.denominator_ne_zero h.2
    simp only [rationalEval,numerator,denominator,eval₂_add,eval₂_mul,eval₂_C,
      rational_castHom_apply,Int.cast_mul,ia h.1,ib h.2]
    field_simp
  | sub a b ia ib =>
    have ha : (a.denominator:ℚ)≠0 := by exact_mod_cast a.denominator_ne_zero h.1
    have hb : (b.denominator:ℚ)≠0 := by exact_mod_cast b.denominator_ne_zero h.2
    simp only [rationalEval,numerator,denominator,eval₂_sub,eval₂_mul,eval₂_C,
      rational_castHom_apply,Int.cast_mul,ia h.1,ib h.2]
    field_simp
  | mul a b ia ib =>
    simp only [rationalEval,numerator,denominator,eval₂_mul,Int.cast_mul,ia h.1,ib h.2]
    ring
  | divide a d ia =>
    simp only [rationalEval,numerator,denominator,Int.cast_mul,ia h.1]
    exact div_div _ _ _

theorem integerEval_cleared (e:Expr ι) (x:ι→ℤ) (h:e.IntegralAt x) :
    e.denominator*e.integerEval x=eval x e.numerator := by
  induction e with
  | atom i => simp [integerEval,numerator,denominator]
  | fixed c => simp [integerEval,numerator,denominator]
  | add a b ia ib =>
    simp only [integerEval,numerator,denominator,eval_add,eval_mul,eval_C]
    rw [← ia h.1,← ib h.2]
    ring
  | sub a b ia ib =>
    simp only [integerEval,numerator,denominator,eval_sub,eval_mul,eval_C]
    rw [← ia h.1,← ib h.2]
    ring
  | mul a b ia ib =>
    simp only [integerEval,numerator,denominator,eval_mul]
    rw [← ia h.1,← ib h.2]
    ring
  | divide a d ia =>
    change (a.denominator*d)*(a.integerEval x/d)=eval x a.numerator
    rw [mul_assoc,Int.mul_ediv_cancel' h.2]
    exact ia h.1

def degreeBudget : Expr ι→ℕ
  | .atom _ => 1
  | .fixed _ => 0
  | .add a b => max a.degreeBudget b.degreeBudget
  | .sub a b => max a.degreeBudget b.degreeBudget
  | .mul a b => a.degreeBudget+b.degreeBudget
  | .divide a _ => a.degreeBudget

theorem numerator_degree_le (e:Expr ι) : e.numerator.totalDegree≤e.degreeBudget := by
  have hC (P:MvPolynomial ι ℤ) (d:ℤ) : (P*C d).totalDegree≤P.totalDegree := by
    simpa only [totalDegree_C,add_zero] using totalDegree_mul P (C d)
  induction e with
  | atom i => simp [numerator,degreeBudget]
  | fixed c => simp only [numerator,degreeBudget,totalDegree_C,le_refl]
  | add a b ia ib =>
    exact (totalDegree_add _ _).trans (max_le_max ((hC _ _).trans ia) ((hC _ _).trans ib))
  | sub a b ia ib =>
    change (a.numerator*C b.denominator-b.numerator*C a.denominator).totalDegree≤_
    rw [sub_eq_add_neg]
    apply (totalDegree_add _ _).trans
    rw [totalDegree_neg]
    exact max_le_max ((hC _ _).trans ia) ((hC _ _).trans ib)
  | mul a b ia ib => exact (totalDegree_mul _ _).trans (Nat.add_le_add ia ib)
  | divide a d ia => exact ia

end Expr
end Ostmann.Characters.SymbolicHistory

end

end OAI
