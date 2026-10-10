import Mathlib.Algebra.Polynomial.AlgebraMap

namespace OAI

/-! # Transferring an annihilator from an operator agreeing on the range -/

noncomputable section
namespace PolycyclicRecognition

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

theorem aeval_mul_eq_of_mul_eq (a b : A) (h : a*b = b*b) (p : Polynomial R) :
    Polynomial.aeval a p * b = b * Polynomial.aeval b p := by
  induction p using Polynomial.induction_on with
  | C r =>
    simp only [Polynomial.aeval_C]
    exact Algebra.commutes r b
  | add p q hp hq => simp only [map_add,add_mul,mul_add,hp,hq]
  | monomial k r hk =>
    have he : Polynomial.C r * Polynomial.X^(k+1) =
        (Polynomial.C r * Polynomial.X^k) * Polynomial.X := by rw [pow_succ,mul_assoc]
    have ha : Polynomial.aeval a ((Polynomial.C r * Polynomial.X^k) * Polynomial.X) =
        Polynomial.aeval a (Polynomial.C r * Polynomial.X^k) * a := by
      rw [map_mul,Polynomial.aeval_X]
    have hb : Polynomial.aeval b ((Polynomial.C r * Polynomial.X^k) * Polynomial.X) =
        Polynomial.aeval b (Polynomial.C r * Polynomial.X^k) * b := by
      rw [map_mul,Polynomial.aeval_X]
    rw [he,ha,hb]
    calc
      (Polynomial.aeval a (Polynomial.C r * Polynomial.X^k) * a) * b =
          Polynomial.aeval a (Polynomial.C r * Polynomial.X^k) * (a*b) := mul_assoc _ _ _
      _ = Polynomial.aeval a (Polynomial.C r * Polynomial.X^k) * (b*b) := by rw [h]
      _ = (Polynomial.aeval a (Polynomial.C r * Polynomial.X^k) * b) * b :=
        (mul_assoc _ _ _).symm
      _ = (b * Polynomial.aeval b (Polynomial.C r * Polynomial.X^k)) * b := by rw [hk]
      _ = b * (Polynomial.aeval b (Polynomial.C r * Polynomial.X^k) * b) := mul_assoc _ _ _

theorem aeval_X_mul_eq_zero_of_mul_eq (a b : A) (h : a*b = b*b)
    (p : Polynomial R) (hp : Polynomial.aeval a p = 0) :
    Polynomial.aeval b (Polynomial.X*p) = 0 := by
  rw [map_mul,Polynomial.aeval_X,← aeval_mul_eq_of_mul_eq a b h p,hp,zero_mul]

end PolycyclicRecognition

end

end OAI
