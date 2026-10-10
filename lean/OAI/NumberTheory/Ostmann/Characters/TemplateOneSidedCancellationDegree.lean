import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationBasic

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory TemplateSupportRemoval
variable {ι : Type*} [DecidableEq ι]

@[simp] theorem sectionPolynomial_C (i : ι) (x : Other i → ℤ) (c : ℤ) :
    sectionPolynomial i x (MvPolynomial.C c) = Polynomial.C (c:ℝ) := by
  rw [sectionPolynomial,MvPolynomial.eval₂_C]
  simp

theorem section_numerator_degree_le (i : ι) (x : Other i → ℤ) (e : Expr ι) :
    (sectionPolynomial i x e.numerator).natDegree ≤ e.degreeBudget := by
  have hC (P : MvPolynomial ι ℤ) (d : ℤ) :
      (sectionPolynomial i x (P*MvPolynomial.C d)).natDegree ≤
        (sectionPolynomial i x P).natDegree := by
    rw [show sectionPolynomial i x (P*MvPolynomial.C d)=
      sectionPolynomial i x P*sectionPolynomial i x (MvPolynomial.C d) from
        MvPolynomial.eval₂_mul _ _,sectionPolynomial_C]
    exact Polynomial.natDegree_mul_C_le _ _
  induction e with
  | atom j =>
    by_cases hj : j=i <;> simp [Expr.numerator,Expr.degreeBudget,sectionPolynomial,hj]
  | fixed c =>
    change (sectionPolynomial i x (MvPolynomial.C c)).natDegree ≤ 0
    rw [sectionPolynomial_C,Polynomial.natDegree_C]
  | add a b ia ib =>
    change (sectionPolynomial i x (a.numerator*MvPolynomial.C b.denominator+
      b.numerator*MvPolynomial.C a.denominator)).natDegree ≤ _
    rw [show sectionPolynomial i x (a.numerator*MvPolynomial.C b.denominator+
      b.numerator*MvPolynomial.C a.denominator)=
      sectionPolynomial i x (a.numerator*MvPolynomial.C b.denominator)+
        sectionPolynomial i x (b.numerator*MvPolynomial.C a.denominator) from MvPolynomial.eval₂_add _ _]
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le_max ((hC _ _).trans ia) ((hC _ _).trans ib))
  | sub a b ia ib =>
    change (sectionPolynomial i x (a.numerator*MvPolynomial.C b.denominator-
      b.numerator*MvPolynomial.C a.denominator)).natDegree ≤ _
    rw [show sectionPolynomial i x (a.numerator*MvPolynomial.C b.denominator-
      b.numerator*MvPolynomial.C a.denominator)=
      sectionPolynomial i x (a.numerator*MvPolynomial.C b.denominator)-
        sectionPolynomial i x (b.numerator*MvPolynomial.C a.denominator) from MvPolynomial.eval₂_sub _ _ _]
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le_max ((hC _ _).trans ia) ((hC _ _).trans ib))
  | mul a b ia ib =>
    change (sectionPolynomial i x (a.numerator*b.numerator)).natDegree ≤ _
    rw [show sectionPolynomial i x (a.numerator*b.numerator)=
      sectionPolynomial i x a.numerator*sectionPolynomial i x b.numerator from MvPolynomial.eval₂_mul _ _]
    exact (Polynomial.natDegree_mul_le).trans (Nat.add_le_add ia ib)
  | divide a d ia => exact ia

theorem argument_degree_le (i : ι) (x : Other i → ℤ) (e : Expr ι) :
    (argument i x e).natDegree ≤ e.degreeBudget :=
  (Polynomial.natDegree_C_mul_le _ _).trans (section_numerator_degree_le i x e)

theorem guard_degree_le (g : Guard ι) (i : ι) (x : Other i → ℤ) :
    (g.polynomial i x).natDegree ≤ g.expression.degreeBudget := by
  unfold Guard.polynomial
  split_ifs
  · exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le (argument_degree_le _ _ _) (by rw [Polynomial.natDegree_C]; omega))
  · exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le (by rw [Polynomial.natDegree_C]; omega) (argument_degree_le _ _ _))

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
