import OAI.NumberTheory.Ostmann.Characters.SymbolicHistory

namespace OAI

noncomputable section
namespace Ostmann.Characters.SymbolicHistory
open MvPolynomial
variable {ι:Type*}

theorem polynomial_modEq (P:MvPolynomial ι ℤ) (x y:ι→ℤ) (N:ℤ)
    (h:∀i,x i≡y i [ZMOD N]) : eval x P≡eval y P [ZMOD N] := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa only [eval_C] using (Int.ModEq.refl c : c≡c [ZMOD N])
  | add P Q ih ih' => simpa only [eval_add] using ih.add ih'
  | mul_X P i ih => simpa only [eval_mul,eval_X] using ih.mul (h i)

namespace Expr

theorem integerEval_modEq (e:Expr ι) (x y:ι→ℤ) (N:ℤ) (he:e.Valid)
    (hx:e.IntegralAt x) (hy:e.IntegralAt y)
    (h:∀i,x i≡y i [ZMOD e.denominator*N]) :
    e.integerEval x≡e.integerEval y [ZMOD N] := by
  apply Int.ModEq.mul_left_cancel' (e.denominator_ne_zero he)
  rw [e.integerEval_cleared x hx,e.integerEval_cleared y hy]
  exact polynomial_modEq e.numerator x y _ h

def supportModulus : Expr ι→ℤ
  | .atom _ => 1
  | .fixed _ => 1
  | .add a b => a.supportModulus*b.supportModulus
  | .sub a b => a.supportModulus*b.supportModulus
  | .mul a b => a.supportModulus*b.supportModulus
  | .divide a d => a.supportModulus*(a.denominator*d)

theorem supportModulus_ne_zero (e:Expr ι) (he:e.Valid) : e.supportModulus≠0 := by
  induction e with
  | atom i => exact one_ne_zero
  | fixed c => exact one_ne_zero
  | add a b ia ib => exact mul_ne_zero (ia he.1) (ib he.2)
  | sub a b ia ib => exact mul_ne_zero (ia he.1) (ib he.2)
  | mul a b ia ib => exact mul_ne_zero (ia he.1) (ib he.2)
  | divide a d ia =>
    exact mul_ne_zero (ia he.1) (mul_ne_zero (a.denominator_ne_zero he.1) he.2)

theorem integralAt_iff_of_modEq (e:Expr ι) (he:e.Valid) (x y:ι→ℤ)
    (h:∀i,x i≡y i [ZMOD e.supportModulus]) : e.IntegralAt x↔e.IntegralAt y := by
  induction e with
  | atom i => rfl
  | fixed c => rfl
  | add a b ia ib =>
    exact and_congr
      (ia he.1 (fun i=>(h i).of_dvd (dvd_mul_right _ _)))
      (ib he.2 (fun i=>(h i).of_dvd (dvd_mul_left _ _)))
  | sub a b ia ib =>
    exact and_congr
      (ia he.1 (fun i=>(h i).of_dvd (dvd_mul_right _ _)))
      (ib he.2 (fun i=>(h i).of_dvd (dvd_mul_left _ _)))
  | mul a b ia ib =>
    exact and_congr
      (ia he.1 (fun i=>(h i).of_dvd (dvd_mul_right _ _)))
      (ib he.2 (fun i=>(h i).of_dvd (dvd_mul_left _ _)))
  | divide a d ia =>
    have hab : a.IntegralAt x↔a.IntegralAt y :=
      ia he.1 (fun i=>(h i).of_dvd (dvd_mul_right _ _))
    change (a.IntegralAt x ∧ d∣a.integerEval x) ↔
      (a.IntegralAt y ∧ d∣a.integerEval y)
    constructor
    · intro hx
      have hy := hab.mp hx.1
      exact ⟨hy,(a.integerEval_modEq x y d he.1 hx.1 hy
        (fun i=>(h i).of_dvd (dvd_mul_left _ _))).dvd_iff.mp hx.2⟩
    · intro hy
      have hx := hab.mpr hy.1
      exact ⟨hx,(a.integerEval_modEq x y d he.1 hx hy.1
        (fun i=>(h i).of_dvd (dvd_mul_left _ _))).dvd_iff.mpr hy.2⟩

end Expr
end Ostmann.Characters.SymbolicHistory

end

end OAI
