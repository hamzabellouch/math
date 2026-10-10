import OAI.NumberTheory.Ostmann.Characters.RationalHistory

namespace OAI

noncomputable section
namespace Ostmann.Characters.RationalHistory.Expr
open MvPolynomial
variable {ι K : Type*} [Field K]

def fieldEval (x:ι→K) : Expr ι→K
  | .atom i => x i
  | .fixed c => c
  | .add a b => a.fieldEval x+b.fieldEval x
  | .sub a b => a.fieldEval x-b.fieldEval x
  | .mul a b => a.fieldEval x*b.fieldEval x
  | .divide a b => a.fieldEval x/b.fieldEval x

def FieldRegularAt (x:ι→K) : Expr ι→Prop
  | .atom _ => True
  | .fixed _ => True
  | .add a b => a.FieldRegularAt x ∧ b.FieldRegularAt x
  | .sub a b => a.FieldRegularAt x ∧ b.FieldRegularAt x
  | .mul a b => a.FieldRegularAt x ∧ b.FieldRegularAt x
  | .divide a b => a.FieldRegularAt x ∧ b.FieldRegularAt x ∧ b.fieldEval x≠0

private theorem field_cast_apply (c:ℤ) : (Int.castRingHom K) c=(c:K) := rfl

theorem field_cleared (e:Expr ι) (x:ι→K) (h:e.FieldRegularAt x) :
    eval₂ (Int.castRingHom K) x e.denominator≠0 ∧
    eval₂ (Int.castRingHom K) x e.denominator*e.fieldEval x=
      eval₂ (Int.castRingHom K) x e.numerator := by
  induction e with
  | atom i => simp only [numerator,denominator,fraction,fieldEval,eval₂_one,eval₂_X,one_mul,ne_eq,one_ne_zero,not_false_eq_true,and_self]
  | fixed c => simp only [numerator,denominator,fraction,fieldEval,eval₂_one,eval₂_C,field_cast_apply,one_mul,ne_eq,one_ne_zero,not_false_eq_true,and_self]
  | add a b ia ib =>
    obtain ⟨ha,ea⟩ := ia h.1
    obtain ⟨hb,eb⟩ := ib h.2
    simp only [numerator,denominator,fraction,fieldEval,eval₂_mul,eval₂_add] at ea eb ⊢
    refine ⟨mul_ne_zero ha hb,?_⟩
    rw [← ea,← eb]
    ring
  | sub a b ia ib =>
    obtain ⟨ha,ea⟩ := ia h.1
    obtain ⟨hb,eb⟩ := ib h.2
    simp only [numerator,denominator,fraction,fieldEval,eval₂_mul,eval₂_sub] at ea eb ⊢
    refine ⟨mul_ne_zero ha hb,?_⟩
    rw [← ea,← eb]
    ring
  | mul a b ia ib =>
    obtain ⟨ha,ea⟩ := ia h.1
    obtain ⟨hb,eb⟩ := ib h.2
    simp only [numerator,denominator,fraction,fieldEval,eval₂_mul] at ea eb ⊢
    refine ⟨mul_ne_zero ha hb,?_⟩
    rw [← ea,← eb]
    ring
  | divide a b ia ib =>
    obtain ⟨ha,ea⟩ := ia h.1
    obtain ⟨hb,eb⟩ := ib h.2.1
    have hbn : eval₂ (Int.castRingHom K) x b.numerator≠0 := by
      rw [← eb]
      exact mul_ne_zero hb h.2.2
    simp only [numerator,denominator,fraction,fieldEval,eval₂_mul] at ea eb ⊢
    refine ⟨mul_ne_zero ha hbn,?_⟩
    rw [← ea,← eb]
    field_simp [h.2.2]

theorem fieldEval_eq (e:Expr ι) (x:ι→K) (h:e.FieldRegularAt x) :
    e.fieldEval x=eval₂ (Int.castRingHom K) x e.numerator/
      eval₂ (Int.castRingHom K) x e.denominator := by
  obtain ⟨hd,he⟩ := e.field_cleared x h
  apply (eq_div_iff hd).mpr
  simpa only [mul_comm] using he

end Ostmann.Characters.RationalHistory.Expr

end

end OAI
