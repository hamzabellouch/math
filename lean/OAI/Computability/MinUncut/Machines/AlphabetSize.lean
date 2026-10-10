import Mathlib
import OAI.Computability.MinUncut.Machines.FiniteAlphabetBounds
import OAI.Computability.MinUncut.Search.ArithmeticExpression

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteProof
attribute [local instance] Classical.propDecidable
variable {Name I : Type*} [Fintype I] [Fintype Name]
lemma variable_card_bound {L : ℕ} (hN : Fintype.card Name≤L) :
    Fintype.card (FamilyVariable Name I)≤
      ((2*L^3)^Fintype.card I+(L+2*L^3)^Fintype.card I)*2^(2^(3*Fintype.card I)) := by
  have hcard : Fintype.card (FamilyVariable Name I)≤
      ((2*Fintype.card Name^3)^Fintype.card I+
       (Fintype.card Name+2*Fintype.card Name^3)^Fintype.card I)*2^(2^(3*Fintype.card I)) := by
    rw [← familyQuestion_card]
    exact familyVariable_card_le
  have h3 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hN 3)
  have ha := Nat.pow_le_pow_left h3 (Fintype.card I)
  have hb := Nat.pow_le_pow_left (Nat.add_le_add hN h3) (Fintype.card I)
  exact hcard.trans (Nat.mul_le_mul_right _ (Nat.add_le_add ha hb))
lemma variable_nat_card_bound {L : ℕ} (hN : Fintype.card Name≤L) :
    Nat.card (FamilyVariable Name I)≤
      ((2*L^3)^Fintype.card I+(L+2*L^3)^Fintype.card I)*2^(2^(3*Fintype.card I)) := by
  rw [Nat.card_eq_fintype_card]
  exact variable_card_bound (Name := Name) (I := I) hN

def alphabetSizePolynomial (t : ℕ) : Polynomial ℕ :=
  ((Polynomial.C 2*Polynomial.X^3)^t+
    (Polynomial.X+Polynomial.C 2*Polynomial.X^3)^t)*Polynomial.C (2^(2^(3*t)))

lemma alphabetSizePolynomial_bound {Name : Type*} [Fintype Name] (t L : ℕ)
    (hN : Fintype.card Name≤L) :
    Fintype.card (FamilyVariable Name (Fin t))≤(alphabetSizePolynomial t).eval L := by
  have hh := variable_nat_card_bound (Name := Name) (I := Fin t) (L := L) hN
  have hr : ((2*L^3)^Fintype.card (Fin t)+(L+2*L^3)^Fintype.card (Fin t))*
      2^(2^(3*Fintype.card (Fin t)))=(alphabetSizePolynomial t).eval L := by
    simp only [Fintype.card_fin,alphabetSizePolynomial,Polynomial.eval_mul,Polynomial.eval_add,
      Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_X]
  rw [← Nat.card_eq_fintype_card]
  exact Nat.le_trans hh (Nat.le_of_eq hr)
end MinUncut.Outer

end
end

end OAI
