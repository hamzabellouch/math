import OAI.NumberTheory.Ostmann.Characters.SymbolicHistory

namespace OAI

noncomputable section
namespace Ostmann.Characters.SymbolicHistory.Expr
open MvPolynomial
variable {ι : Type*}

def syntaxSize : Expr ι → ℕ
  | .atom _ => 1
  | .fixed _ => 1
  | .add a b => a.syntaxSize+b.syntaxSize+1
  | .sub a b => a.syntaxSize+b.syntaxSize+1
  | .mul a b => a.syntaxSize+b.syntaxSize+1
  | .divide a _ => a.syntaxSize+1

def FixedBound (B : ℝ) : Expr ι → Prop
  | .atom _ => True
  | .fixed c => |(c:ℝ)|≤B
  | .add a b => a.FixedBound B ∧ b.FixedBound B
  | .sub a b => a.FixedBound B ∧ b.FixedBound B
  | .mul a b => a.FixedBound B ∧ b.FixedBound B
  | .divide a d => a.FixedBound B ∧ |(d:ℝ)|≤B

def FixedLogBound (H : ℝ) (e : Expr ι) : Prop := e.FixedBound (Real.exp H)

private theorem abs_mul_le {a b A B : ℝ} (ha : |a|≤A) (hb : |b|≤B) :
    |a*b|≤A*B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

private theorem product_budget {B : ℝ} (hB : 2≤B) (a b : ℕ) :
    B^a*B^b≤B^(a+b+1) := by
  rw [pow_succ,pow_add]
  exact le_mul_of_one_le_right (by positivity) (by linarith)

private theorem addition_budget {B : ℝ} (hB : 2≤B) (a b : ℕ) :
    2*(B^a*B^b)≤B^(a+b+1) := by
  rw [pow_succ,pow_add]
  nlinarith [mul_le_mul_of_nonneg_right hB (by positivity : 0≤B^a*B^b)]

theorem cleared_abs_le_pow_size (e : Expr ι) {B : ℝ} (hB : 2≤B)
    (he : e.FixedBound B) (x : ι → ℝ) (hx : ∀i,|x i|≤B) :
    |eval₂ (Int.castRingHom ℝ) x e.numerator|≤B^e.syntaxSize ∧
      |(e.denominator:ℝ)|≤B^e.syntaxSize := by
  have hB1 : 1≤B := by linarith
  induction e with
  | atom i =>
    simpa only [numerator,denominator,syntaxSize,eval₂_X,Int.cast_one,abs_one,pow_one] using
      And.intro (hx i) hB1
  | fixed c =>
    simp only [numerator,denominator,syntaxSize,eval₂_C,Int.cast_one]
    change |(c:ℝ)|≤B^1 ∧ |(1:ℝ)|≤B^1
    simpa only [FixedBound,pow_one,abs_one] using And.intro he hB1
  | add a b ia ib =>
    have ha := ia he.1
    have hb := ib he.2
    have had := abs_mul_le ha.1 hb.2
    have hbc := abs_mul_le hb.1 ha.2
    have hdd := abs_mul_le ha.2 hb.2
    simp only [numerator,denominator,syntaxSize,eval₂_add,eval₂_mul,eval₂_C,Int.cast_mul]
    change |eval₂ (Int.castRingHom ℝ) x a.numerator*(b.denominator:ℝ)+
      eval₂ (Int.castRingHom ℝ) x b.numerator*(a.denominator:ℝ)|≤_ ∧ _
    refine ⟨?_,hdd.trans (product_budget hB _ _)⟩
    apply (abs_add_le _ _).trans
    apply (add_le_add had hbc).trans
    have h := addition_budget hB a.syntaxSize b.syntaxSize
    nlinarith
  | sub a b ia ib =>
    have ha := ia he.1
    have hb := ib he.2
    have had := abs_mul_le ha.1 hb.2
    have hbc := abs_mul_le hb.1 ha.2
    have hdd := abs_mul_le ha.2 hb.2
    simp only [numerator,denominator,syntaxSize,eval₂_sub,eval₂_mul,eval₂_C,Int.cast_mul]
    change |eval₂ (Int.castRingHom ℝ) x a.numerator*(b.denominator:ℝ)-
      eval₂ (Int.castRingHom ℝ) x b.numerator*(a.denominator:ℝ)|≤_ ∧ _
    refine ⟨?_,hdd.trans (product_budget hB _ _)⟩
    apply (abs_sub _ _).trans
    apply (add_le_add had hbc).trans
    have h := addition_budget hB a.syntaxSize b.syntaxSize
    nlinarith
  | mul a b ia ib =>
    have ha := ia he.1
    have hb := ib he.2
    simp only [numerator,denominator,syntaxSize,eval₂_mul,Int.cast_mul]
    exact ⟨(abs_mul_le ha.1 hb.1).trans (product_budget hB _ _),
      (abs_mul_le ha.2 hb.2).trans (product_budget hB _ _)⟩
  | divide a d ia =>
    have ha := ia he.1
    simp only [numerator,denominator,syntaxSize,Int.cast_mul]
    refine ⟨ha.1.trans (pow_le_pow_right₀ hB1 (by omega)),?_⟩
    simpa only [pow_succ] using abs_mul_le ha.2 he.2

end Ostmann.Characters.SymbolicHistory.Expr

end

end OAI
