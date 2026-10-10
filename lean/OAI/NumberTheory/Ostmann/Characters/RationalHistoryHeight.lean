import OAI.NumberTheory.Ostmann.Characters.RationalHistory

namespace OAI

noncomputable section
namespace Ostmann.Characters.RationalHistory.Expr
open MvPolynomial
variable {ι:Type*}

def heightBudget (B:ℝ) : Expr ι→ℝ
  | .atom _ => B
  | .fixed c => max 1 |(c:ℝ)|
  | .add a b => 2*a.heightBudget B*b.heightBudget B
  | .sub a b => 2*a.heightBudget B*b.heightBudget B
  | .mul a b => a.heightBudget B*b.heightBudget B
  | .divide a b => a.heightBudget B*b.heightBudget B

private theorem abs_mul_le {a b A B:ℝ} (ha:|a|≤A) (hb:|b|≤B) : |a*b|≤A*B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

private theorem abs_add_products_le {a b c d A B:ℝ}
    (ha:|a|≤A) (hb:|b|≤A) (hc:|c|≤B) (hd:|d|≤B) :
    |a*d+c*b|≤2*A*B := by
  calc
    _ ≤ |a*d|+|c*b| := abs_add_le _ _
    _ ≤ A*B+B*A := add_le_add (abs_mul_le ha hd) (abs_mul_le hc hb)
    _ = _ := by ring

private theorem abs_sub_products_le {a b c d A B:ℝ}
    (ha:|a|≤A) (hb:|b|≤A) (hc:|c|≤B) (hd:|d|≤B) :
    |a*d-c*b|≤2*A*B := by
  calc
    _ ≤ |a*d|+|c*b| := abs_sub _ _
    _ ≤ A*B+B*A := add_le_add (abs_mul_le ha hd) (abs_mul_le hc hb)
    _ = _ := by ring

private theorem real_cast_apply (c:ℤ) : (Int.castRingHom ℝ) c=(c:ℝ) := rfl

theorem fraction_eval_abs_le (e:Expr ι) (x:ι→ℝ) (B:ℝ) (hB:1≤B)
    (hx:∀i,|x i|≤B) :
    |eval₂ (Int.castRingHom ℝ) x e.numerator|≤e.heightBudget B ∧
    |eval₂ (Int.castRingHom ℝ) x e.denominator|≤e.heightBudget B := by
  induction e with
  | atom i => simpa only [numerator,denominator,fraction,heightBudget,eval₂_X,eval₂_one,abs_one] using And.intro (hx i) hB
  | fixed c =>
    simp only [numerator,denominator,fraction,heightBudget,eval₂_C,eval₂_one,real_cast_apply,abs_one]
    exact ⟨le_max_right _ _,le_max_left _ _⟩
  | add a b ia ib =>
    have ha : 0≤a.heightBudget B := (abs_nonneg _).trans ia.1
    have hb : 0≤b.heightBudget B := (abs_nonneg _).trans ib.1
    simp only [numerator,denominator,fraction,heightBudget,eval₂_add,eval₂_mul] at ia ib ⊢
    refine ⟨abs_add_products_le ia.1 ia.2 ib.1 ib.2,?_⟩
    exact (abs_mul_le ia.2 ib.2).trans (by nlinarith [mul_nonneg ha hb])
  | sub a b ia ib =>
    have ha : 0≤a.heightBudget B := (abs_nonneg _).trans ia.1
    have hb : 0≤b.heightBudget B := (abs_nonneg _).trans ib.1
    simp only [numerator,denominator,fraction,heightBudget,eval₂_sub,eval₂_mul] at ia ib ⊢
    refine ⟨abs_sub_products_le ia.1 ia.2 ib.1 ib.2,?_⟩
    exact (abs_mul_le ia.2 ib.2).trans (by nlinarith [mul_nonneg ha hb])
  | mul a b ia ib =>
    simp only [numerator,denominator,fraction,heightBudget,eval₂_mul] at ia ib ⊢
    exact ⟨abs_mul_le ia.1 ib.1,abs_mul_le ia.2 ib.2⟩
  | divide a b ia ib =>
    simp only [numerator,denominator,fraction,heightBudget,eval₂_mul] at ia ib ⊢
    exact ⟨abs_mul_le ia.1 ib.2,abs_mul_le ia.2 ib.1⟩

end Ostmann.Characters.RationalHistory.Expr

end

end OAI
