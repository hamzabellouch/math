import OAI.NumberTheory.Ostmann.Characters.RationalHistory

namespace OAI

noncomputable section
namespace Ostmann.Characters.RationalHistory.Expr
open MvPolynomial
variable {ι:Type*}

def atomCount : Expr ι→ℕ
  | .atom _ => 1
  | .fixed _ => 0
  | .add a b => atomCount a+atomCount b
  | .sub a b => atomCount a+atomCount b
  | .mul a b => atomCount a+atomCount b
  | .divide a b => atomCount a+atomCount b

theorem fraction_degree_le (e:Expr ι) :
    e.numerator.totalDegree≤e.atomCount ∧ e.denominator.totalDegree≤e.atomCount := by
  induction e with
  | atom i => simp only [numerator,denominator,fraction,atomCount,totalDegree_X,totalDegree_one]; omega
  | fixed c => simp only [numerator,denominator,fraction,atomCount,totalDegree_C,totalDegree_one]; omega
  | add a b ia ib =>
    change (a.numerator*b.denominator+b.numerator*a.denominator).totalDegree≤_ ∧
      (a.denominator*b.denominator).totalDegree≤_
    refine ⟨(totalDegree_add _ _).trans (max_le ?_ ?_),?_⟩
    · exact (totalDegree_mul _ _).trans (Nat.add_le_add ia.1 ib.2)
    · exact (totalDegree_mul _ _).trans (by simpa only [atomCount, Nat.add_comm] using Nat.add_le_add ib.1 ia.2)
    · exact (totalDegree_mul _ _).trans (Nat.add_le_add ia.2 ib.2)
  | sub a b ia ib =>
    change (a.numerator*b.denominator-b.numerator*a.denominator).totalDegree≤_ ∧
      (a.denominator*b.denominator).totalDegree≤_
    rw [sub_eq_add_neg]
    refine ⟨(totalDegree_add _ _).trans (max_le ?_ ?_),?_⟩
    · exact (totalDegree_mul _ _).trans (Nat.add_le_add ia.1 ib.2)
    · rw [totalDegree_neg]
      exact (totalDegree_mul _ _).trans (by simpa only [atomCount, Nat.add_comm] using Nat.add_le_add ib.1 ia.2)
    · exact (totalDegree_mul _ _).trans (Nat.add_le_add ia.2 ib.2)
  | mul a b ia ib => exact ⟨(totalDegree_mul _ _).trans (Nat.add_le_add ia.1 ib.1),
      (totalDegree_mul _ _).trans (Nat.add_le_add ia.2 ib.2)⟩
  | divide a b ia ib => exact ⟨(totalDegree_mul _ _).trans (Nat.add_le_add ia.1 ib.2),
      (totalDegree_mul _ _).trans (Nat.add_le_add ia.2 ib.1)⟩

end Ostmann.Characters.RationalHistory.Expr

end

end OAI
