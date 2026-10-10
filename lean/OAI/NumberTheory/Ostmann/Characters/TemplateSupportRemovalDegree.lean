import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalCoordinates

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateSupportRemoval
open MvPolynomial SymbolicHistory
variable {ι : Type*} [DecidableEq ι]

@[simp] theorem eraseCoordinate_C (i : ι) (c : ℤ) : eraseCoordinate i (C c)=C c := by
  simp [eraseCoordinate]

theorem erased_numerator_degree_le (i : ι) (e : Expr ι) :
    (eraseCoordinate i e.numerator).totalDegree ≤ e.degreeBudget := by
  have hC (P : MvPolynomial ι ℤ) (d : ℤ) :
      (eraseCoordinate i (P*C d)).totalDegree ≤ (eraseCoordinate i P).totalDegree := by
    rw [map_mul,eraseCoordinate_C]
    simpa only [totalDegree_C,add_zero] using totalDegree_mul (eraseCoordinate i P) (C d)
  induction e with
  | atom j =>
    by_cases hj : j=i <;> simp [Expr.numerator,Expr.degreeBudget,eraseCoordinate,hj]
  | fixed c =>
    change (eraseCoordinate i (C c)).totalDegree ≤ 0
    rw [eraseCoordinate_C,totalDegree_C]
  | add a b ia ib =>
    change (eraseCoordinate i (a.numerator*C b.denominator+b.numerator*C a.denominator)).totalDegree≤_
    rw [map_add]
    exact (totalDegree_add _ _).trans (max_le_max ((hC _ _).trans ia) ((hC _ _).trans ib))
  | sub a b ia ib =>
    change (eraseCoordinate i (a.numerator*C b.denominator-b.numerator*C a.denominator)).totalDegree≤_
    rw [map_sub,sub_eq_add_neg]
    apply (totalDegree_add _ _).trans
    rw [totalDegree_neg]
    exact max_le_max ((hC _ _).trans ia) ((hC _ _).trans ib)
  | mul a b ia ib =>
    change (eraseCoordinate i (a.numerator*b.numerator)).totalDegree≤_
    rw [map_mul]
    exact (totalDegree_mul _ _).trans (Nat.add_le_add ia ib)
  | divide a d ia => exact ia

end Ostmann.Characters.TemplateSupportRemoval

end

end OAI
