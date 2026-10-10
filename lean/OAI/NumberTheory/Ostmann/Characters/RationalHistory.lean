import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Characters.RationalHistory
open MvPolynomial

inductive Expr (ι:Type*)
  | atom (i:ι)
  | fixed (c:ℤ)
  | add (a b:Expr ι)
  | sub (a b:Expr ι)
  | mul (a b:Expr ι)
  | divide (a b:Expr ι)

namespace Expr
variable {ι:Type*}

def fraction : Expr ι→MvPolynomial ι ℤ × MvPolynomial ι ℤ
  | .atom i => (X i,1)
  | .fixed c => (C c,1)
  | .add a b => (a.fraction.1*b.fraction.2+b.fraction.1*a.fraction.2,
      a.fraction.2*b.fraction.2)
  | .sub a b => (a.fraction.1*b.fraction.2-b.fraction.1*a.fraction.2,
      a.fraction.2*b.fraction.2)
  | .mul a b => (a.fraction.1*b.fraction.1,a.fraction.2*b.fraction.2)
  | .divide a b => (a.fraction.1*b.fraction.2,a.fraction.2*b.fraction.1)

def numerator (e:Expr ι) := e.fraction.1
def denominator (e:Expr ι) := e.fraction.2

def rationalEval (x:ι→ℚ) : Expr ι→ℚ
  | .atom i => x i
  | .fixed c => c
  | .add a b => a.rationalEval x+b.rationalEval x
  | .sub a b => a.rationalEval x-b.rationalEval x
  | .mul a b => a.rationalEval x*b.rationalEval x
  | .divide a b => a.rationalEval x/b.rationalEval x

def RegularAt (x:ι→ℚ) : Expr ι→Prop
  | .atom _ => True
  | .fixed _ => True
  | .add a b => a.RegularAt x ∧ b.RegularAt x
  | .sub a b => a.RegularAt x ∧ b.RegularAt x
  | .mul a b => a.RegularAt x ∧ b.RegularAt x
  | .divide a b => a.RegularAt x ∧ b.RegularAt x ∧ b.rationalEval x≠0

def integerEval (x:ι→ℤ) : Expr ι→ℤ
  | .atom i => x i
  | .fixed c => c
  | .add a b => a.integerEval x+b.integerEval x
  | .sub a b => a.integerEval x-b.integerEval x
  | .mul a b => a.integerEval x*b.integerEval x
  | .divide a b => a.integerEval x/b.integerEval x

def IntegralAt (x:ι→ℤ) : Expr ι→Prop
  | .atom _ => True
  | .fixed _ => True
  | .add a b => a.IntegralAt x ∧ b.IntegralAt x
  | .sub a b => a.IntegralAt x ∧ b.IntegralAt x
  | .mul a b => a.IntegralAt x ∧ b.IntegralAt x
  | .divide a b => a.IntegralAt x ∧ b.IntegralAt x ∧ b.integerEval x∣a.integerEval x

private theorem cast_apply (c:ℤ) : (Int.castRingHom ℚ) c=(c:ℚ) := rfl

theorem rational_cleared (e:Expr ι) (x:ι→ℚ) (h:e.RegularAt x) :
    eval₂ (Int.castRingHom ℚ) x e.denominator≠0 ∧
    eval₂ (Int.castRingHom ℚ) x e.denominator*e.rationalEval x=
      eval₂ (Int.castRingHom ℚ) x e.numerator := by
  induction e with
  | atom i => simp only [numerator,denominator,fraction,rationalEval,eval₂_one,eval₂_X,one_mul,ne_eq,one_ne_zero,not_false_eq_true,and_self]
  | fixed c => simp only [numerator,denominator,fraction,rationalEval,eval₂_one,eval₂_C,cast_apply,one_mul,ne_eq,one_ne_zero,not_false_eq_true,and_self]
  | add a b ia ib =>
    obtain ⟨ha,ea⟩ := ia h.1
    obtain ⟨hb,eb⟩ := ib h.2
    simp only [numerator,denominator,fraction,rationalEval,eval₂_mul,eval₂_add] at ea eb ⊢
    refine ⟨mul_ne_zero ha hb,?_⟩
    rw [← ea,← eb]
    ring
  | sub a b ia ib =>
    obtain ⟨ha,ea⟩ := ia h.1
    obtain ⟨hb,eb⟩ := ib h.2
    simp only [numerator,denominator,fraction,rationalEval,eval₂_mul,eval₂_sub] at ea eb ⊢
    refine ⟨mul_ne_zero ha hb,?_⟩
    rw [← ea,← eb]
    ring
  | mul a b ia ib =>
    obtain ⟨ha,ea⟩ := ia h.1
    obtain ⟨hb,eb⟩ := ib h.2
    simp only [numerator,denominator,fraction,rationalEval,eval₂_mul] at ea eb ⊢
    refine ⟨mul_ne_zero ha hb,?_⟩
    rw [← ea,← eb]
    ring
  | divide a b ia ib =>
    obtain ⟨ha,ea⟩ := ia h.1
    obtain ⟨hb,eb⟩ := ib h.2.1
    have hbn : eval₂ (Int.castRingHom ℚ) x b.numerator≠0 := by
      rw [← eb]
      exact mul_ne_zero hb h.2.2
    simp only [numerator,denominator,fraction,rationalEval,eval₂_mul] at ea eb ⊢
    refine ⟨mul_ne_zero ha hbn,?_⟩
    rw [← ea,← eb]
    field_simp [h.2.2]

theorem rationalEval_eq (e:Expr ι) (x:ι→ℚ) (h:e.RegularAt x) :
    e.rationalEval x=eval₂ (Int.castRingHom ℚ) x e.numerator/
      eval₂ (Int.castRingHom ℚ) x e.denominator := by
  obtain ⟨hd,he⟩ := e.rational_cleared x h
  apply (eq_div_iff hd).mpr
  simpa only [mul_comm] using he

theorem integerEval_cleared (e:Expr ι) (x:ι→ℤ) (h:e.IntegralAt x) :
    eval x e.denominator*e.integerEval x=eval x e.numerator := by
  induction e with
  | atom i => simp only [numerator,denominator,fraction,integerEval,map_one,eval_X,one_mul]
  | fixed c => simp only [numerator,denominator,fraction,integerEval,map_one,eval_C,one_mul]
  | add a b ia ib =>
    have ea := ia h.1
    have eb := ib h.2
    simp only [numerator,denominator,fraction,integerEval,eval_mul,eval_add] at ea eb ⊢
    rw [← ea,← eb]
    ring
  | sub a b ia ib =>
    have ea := ia h.1
    have eb := ib h.2
    simp only [numerator,denominator,fraction,integerEval,eval_mul,eval_sub] at ea eb ⊢
    rw [← ea,← eb]
    ring
  | mul a b ia ib =>
    have ea := ia h.1
    have eb := ib h.2
    simp only [numerator,denominator,fraction,integerEval,eval_mul] at ea eb ⊢
    rw [← ea,← eb]
    ring
  | divide a b ia ib =>
    have ea := ia h.1
    have eb := ib h.2.1
    simp only [numerator,denominator,fraction,integerEval,eval_mul] at ea eb ⊢
    rw [← ea,← eb]
    calc
      _ = (eval x a.fraction.2*eval x b.fraction.2)*
          (b.integerEval x*(a.integerEval x/b.integerEval x)) := by ring
      _ = _ := by rw [Int.mul_ediv_cancel' h.2.2]; ring

end Expr
end Ostmann.Characters.RationalHistory

end

end OAI
