import OAI.NumberTheory.JointDickman.Analysis.MellinEnergyAlgebra
import OAI.NumberTheory.JointDickman.Counting.ComplexFiniteShortAverages

namespace OAI

/-! # Scaling a two-bounded arithmetic coefficient for the analytic transfer -/
namespace JointDickman
open Finset MeasureTheory PublishedInputs

noncomputable def halfArithmetic (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => f n/2,by simp⟩

lemma halfArithmetic_norm (f : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖≤2) (n : ℕ) :
    ‖halfArithmetic f n‖≤1 := by
  change ‖f n/2‖≤1
  rw [norm_div]
  norm_num
  linarith [hf n]

lemma halfArithmetic_polynomial (f : ArithmeticFunction ℂ) (K : Finset ℕ) (t : ℝ) :
    angularMellinPolynomial K (halfArithmetic f) t = angularMellinPolynomial K f t/2 := by
  rw [←mul_one_div (angularMellinPolynomial K f t) 2,mul_comm]
  rw [←angularMellinPolynomial_const_mul]
  congr 1
  funext n
  change f n/2=(1/2)*f n
  ring

lemma halfArithmetic_energy (f : ArithmeticFunction ℂ) (K : Finset ℕ) (T : ℝ) :
    (∫ t in -T..T, ‖angularMellinPolynomial K (halfArithmetic f) t‖^2) =
      (∫ t in -T..T, ‖angularMellinPolynomial K f t‖^2)/4 := by
  simp_rw [halfArithmetic_polynomial,norm_div,show ‖(2:ℂ)‖=(2:ℝ) by norm_num,div_pow]
  rw [show (2:ℝ)^2=4 by norm_num]
  rw [intervalIntegral.integral_div]

lemma halfArithmetic_short (f : ArithmeticFunction ℂ) (H z : ℝ) :
    complexShortAverage (halfArithmetic f) H z = complexShortAverage f H z/2 := by
  simp only [complexShortAverage,halfArithmetic,ArithmeticFunction.coe_mk]
  rw [←sum_div]
  ring

lemma halfArithmetic_short_energy (f : ArithmeticFunction ℂ) (H X : ℝ) :
    (1/X)*(∫ z in X..2*X, ‖complexShortAverage f H z‖^2) =
      4*((1/X)*(∫ z in X..2*X, ‖complexShortAverage (halfArithmetic f) H z‖^2)) := by
  simp_rw [halfArithmetic_short,norm_div,show ‖(2:ℂ)‖=(2:ℝ) by norm_num,div_pow]
  rw [show (2:ℝ)^2=4 by norm_num]
  rw [intervalIntegral.integral_div]
  ring

end JointDickman

end OAI
