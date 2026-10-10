import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Twist

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryArchimedeanTwist
open ArithmeticFunction

def arithmeticTwist (a : ArithmeticFunction ℂ) (t : ℝ) : ArithmeticFunction ℂ :=
  ⟨twist a t, by simp [twist]⟩

@[simp] lemma arithmeticTwist_apply (a : ArithmeticFunction ℂ) (t : ℝ) (n : ℕ) :
    arithmeticTwist a t n=twist a t n := rfl

lemma arithmeticTwist_mul (a b : ArithmeticFunction ℂ) (t : ℝ) :
    arithmeticTwist (a*b) t=arithmeticTwist a t*arithmeticTwist b t := by
  ext n
  simp only [arithmeticTwist_apply,twist,ArithmeticFunction.mul_apply,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hd1,hd2⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hd
  have he := (Nat.mem_divisorsAntidiagonal.mp hd).1
  rw [←he,Nat.cast_mul,Real.log_mul (by exact_mod_cast hd1) (by exact_mod_cast hd2)]
  simp only [mul_add,Complex.ofReal_add,Complex.exp_add]
  ring
end OrdinaryArchimedeanTwist

end

end OAI
