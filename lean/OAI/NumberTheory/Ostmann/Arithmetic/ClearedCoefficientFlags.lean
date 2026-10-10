import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFieldEvaluation
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySymbolicScope
import OAI.NumberTheory.Ostmann.Characters.RationalHistoryDegree

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.ClearedCoefficientFlags
open Characters.RationalHistory MvPolynomial HistorySymbolicScope
variable {ι K : Type*} [Field K]

def leftCoefficient (a b : Expr ι) : MvPolynomial ι ℤ := a.numerator*b.denominator
def rightCoefficient (a b : Expr ι) : MvPolynomial ι ℤ := b.numerator*a.denominator
def commonDenominator (a b : Expr ι) : MvPolynomial ι ℤ := a.denominator*b.denominator

def minor (a b c d : Expr ι) : MvPolynomial ι ℤ :=
  leftCoefficient a b*rightCoefficient c d-rightCoefficient a b*leftCoefficient c d

theorem coefficients_cleared (a b : Expr ι) (x : ι → K)
    (ha : a.FieldRegularAt x) (hb : b.FieldRegularAt x) :
    eval₂ (Int.castRingHom K) x (commonDenominator a b) ≠ 0 ∧
    eval₂ (Int.castRingHom K) x (leftCoefficient a b) =
      eval₂ (Int.castRingHom K) x (commonDenominator a b)*a.fieldEval x ∧
    eval₂ (Int.castRingHom K) x (rightCoefficient a b) =
      eval₂ (Int.castRingHom K) x (commonDenominator a b)*b.fieldEval x := by
  obtain ⟨ha0,hea⟩ := a.field_cleared x ha
  obtain ⟨hb0,heb⟩ := b.field_cleared x hb
  simp only [commonDenominator,leftCoefficient,rightCoefficient,eval₂_mul]
  refine ⟨mul_ne_zero ha0 hb0,?_,?_⟩
  · rw [← hea]
    ring
  · rw [← heb]
    ring

theorem linear_zero_iff (a b : Expr ι) (x : ι → K)
    (ha : a.FieldRegularAt x) (hb : b.FieldRegularAt x) (X Y : K) :
    eval₂ (Int.castRingHom K) x (leftCoefficient a b)*X+
      eval₂ (Int.castRingHom K) x (rightCoefficient a b)*Y=0 ↔
      a.fieldEval x*X+b.fieldEval x*Y=0 := by
  obtain ⟨h0,ha,hb⟩ := coefficients_cleared a b x ha hb
  rw [ha,hb,mul_assoc,mul_assoc,← mul_add]
  exact mul_eq_zero.trans (or_iff_right h0)

theorem row_nonzero_iff (a b : Expr ι) (x : ι → K)
    (ha : a.FieldRegularAt x) (hb : b.FieldRegularAt x) :
    (eval₂ (Int.castRingHom K) x (leftCoefficient a b) ≠ 0 ∨
      eval₂ (Int.castRingHom K) x (rightCoefficient a b) ≠ 0) ↔
      a.fieldEval x ≠ 0 ∨ b.fieldEval x ≠ 0 := by
  obtain ⟨h0,ha,hb⟩ := coefficients_cleared a b x ha hb
  rw [ha,hb]
  simp only [ne_eq,mul_eq_zero,h0,false_or]

theorem minor_cleared (a b c d : Expr ι) (x : ι → K)
    (ha : a.FieldRegularAt x) (hb : b.FieldRegularAt x)
    (hc : c.FieldRegularAt x) (hd : d.FieldRegularAt x) :
    eval₂ (Int.castRingHom K) x (minor a b c d) =
      (eval₂ (Int.castRingHom K) x (commonDenominator a b)*
        eval₂ (Int.castRingHom K) x (commonDenominator c d))*
      (a.fieldEval x*d.fieldEval x-b.fieldEval x*c.fieldEval x) := by
  obtain ⟨_,h1,h2⟩ := coefficients_cleared a b x ha hb
  obtain ⟨_,h3,h4⟩ := coefficients_cleared c d x hc hd
  simp only [minor,eval₂_sub,eval₂_mul,h1,h2,h3,h4]
  ring

theorem minor_zero_iff (a b c d : Expr ι) (x : ι → K)
    (ha : a.FieldRegularAt x) (hb : b.FieldRegularAt x)
    (hc : c.FieldRegularAt x) (hd : d.FieldRegularAt x) :
    eval₂ (Int.castRingHom K) x (minor a b c d)=0 ↔
      a.fieldEval x*d.fieldEval x-b.fieldEval x*c.fieldEval x=0 := by
  rw [minor_cleared a b c d x ha hb hc hd]
  exact mul_eq_zero.trans (or_iff_right (mul_ne_zero
    (coefficients_cleared a b x ha hb).1 (coefficients_cleared c d x hc hd).1))

theorem coefficient_degrees (a b : Expr ι) :
    (leftCoefficient a b).totalDegree ≤ a.atomCount+b.atomCount ∧
    (rightCoefficient a b).totalDegree ≤ a.atomCount+b.atomCount ∧
    (commonDenominator a b).totalDegree ≤ a.atomCount+b.atomCount := by
  refine ⟨(totalDegree_mul _ _).trans (Nat.add_le_add a.fraction_degree_le.1 b.fraction_degree_le.2),
    ?_,(totalDegree_mul _ _).trans (Nat.add_le_add a.fraction_degree_le.2 b.fraction_degree_le.2)⟩
  exact (totalDegree_mul _ _).trans (by
    simpa only [Nat.add_comm] using
      (Nat.add_le_add b.fraction_degree_le.1 a.fraction_degree_le.2))

theorem minor_degree (a b c d : Expr ι) :
    (minor a b c d).totalDegree ≤ a.atomCount+b.atomCount+(c.atomCount+d.atomCount) := by
  unfold minor
  rw [sub_eq_add_neg]
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact (totalDegree_mul _ _).trans
      (Nat.add_le_add (coefficient_degrees a b).1 (coefficient_degrees c d).2.1)
  · rw [totalDegree_neg]
    exact (totalDegree_mul _ _).trans
      (Nat.add_le_add (coefficient_degrees a b).2.1 (coefficient_degrees c d).1)

def PolynomialAbove [DecidableEq ι] (level : ι → ℕ) (t : ℕ)
    (P : MvPolynomial ι ℤ) : Prop := ∀ i ∈ P.vars, t < level i

theorem polynomialAbove_mul [DecidableEq ι] {level : ι → ℕ} {t : ℕ}
    {P Q : MvPolynomial ι ℤ} (hP : PolynomialAbove level t P)
    (hQ : PolynomialAbove level t Q) : PolynomialAbove level t (P*Q) := by
  intro i hi
  rcases Finset.mem_union.mp (vars_mul P Q hi) with hi | hi
  · exact hP i hi
  · exact hQ i hi

theorem fraction_above [DecidableEq ι] (level : ι → ℕ) (t : ℕ)
    (a : Expr ι) (ha : Above level t a) :
    PolynomialAbove level t a.numerator ∧ PolynomialAbove level t a.denominator :=
  ⟨fun i hi => above_atoms a ha i (a.fraction_vars_subset.1 hi),
    fun i hi => above_atoms a ha i (a.fraction_vars_subset.2 hi)⟩

theorem coefficients_above [DecidableEq ι] (level : ι → ℕ) (t : ℕ)
    (a b : Expr ι) (ha : Above level t a) (hb : Above level t b) :
    PolynomialAbove level t (leftCoefficient a b) ∧
    PolynomialAbove level t (rightCoefficient a b) ∧
    PolynomialAbove level t (commonDenominator a b) :=
  ⟨polynomialAbove_mul (fraction_above level t a ha).1 (fraction_above level t b hb).2,
    polynomialAbove_mul (fraction_above level t b hb).1 (fraction_above level t a ha).2,
    polynomialAbove_mul (fraction_above level t a ha).2 (fraction_above level t b hb).2⟩

theorem minor_above [DecidableEq ι] (level : ι → ℕ) (t : ℕ)
    (a b c d : Expr ι) (ha : Above level t a) (hb : Above level t b)
    (hc : Above level t c) (hd : Above level t d) :
    PolynomialAbove level t (minor a b c d) := by
  have h1 := coefficients_above level t a b ha hb
  have h2 := coefficients_above level t c d hc hd
  intro i hi
  rcases Finset.mem_union.mp ((vars_sub_subset (p := leftCoefficient a b*rightCoefficient c d)
    (q := rightCoefficient a b*leftCoefficient c d)) hi) with hi | hi
  · exact polynomialAbove_mul h1.1 h2.2.1 i hi
  · exact polynomialAbove_mul h1.2.1 h2.1 i hi

end Ostmann.Arithmetic.ClearedCoefficientFlags

end

end OAI
