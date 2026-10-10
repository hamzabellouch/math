import Mathlib

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

namespace OrdinaryLogDerivative
open scoped LSeries.notation
open LSeries ArithmeticFunction

def Complete (f : ℕ → ℂ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → f (m*n) = f m * f n

def mangoldtTwist (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  f n * (ArithmeticFunction.vonMangoldt n : ℂ)

lemma twist_convolution (f g h : ℕ → ℂ) (hf : Complete f) :
    (fun n => f n*g n) ⍟ (fun n => f n*h n) =
      fun n => f n*(g ⍟ h) n := by
  ext n
  simp only [LSeries.convolution_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp1,hp2⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hp
  have he := (Nat.mem_divisorsAntidiagonal.mp hp).1
  rw [← he,hf p.1 p.2 (Nat.pos_of_ne_zero hp1) (Nat.pos_of_ne_zero hp2)]
  ring

lemma mangoldt_convolution (f : ℕ → ℂ) (hf : Complete f) :
    mangoldtTwist f ⍟ f = LSeries.logMul f := by
  have he := twist_convolution f (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
    (1 : ℕ → ℂ) hf
  simp only [Pi.one_apply,mul_one,ArithmeticFunction.convolution_vonMangoldt_const_one] at he
  unfold mangoldtTwist
  rw [he]
  ext n
  exact mul_comm _ _

lemma mangoldt_summable {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (mangoldtTwist f) s := by
  have h := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  rw [LSeriesSummable,←summable_norm_iff] at h ⊢
  apply h.of_nonneg_of_le (fun _ => norm_nonneg _) 
  intro n
  apply LSeries.norm_term_le
  simp only [mangoldtTwist,norm_mul]
  exact (mul_le_mul_of_nonneg_right (hf n) (norm_nonneg _)).trans_eq (one_mul _)

theorem LSeries_derivative_product {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hm : Complete f) {s : ℂ} (hs : 1 < s.re) :
    deriv (LSeries f) s = - (LSeries (mangoldtTwist f) s * LSeries f s) := by
  have hab : LSeries.abscissaOfAbsConv f < s.re :=
    lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_le_const ⟨1,fun n _ => hf n⟩)
      (by exact_mod_cast hs)
  rw [LSeries_deriv hab,←LSeries_convolution' (mangoldt_summable hf hs)
    (LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => hf n) hs),
    mangoldt_convolution f hm]

theorem log_weighted_sum (f : ℕ → ℂ) (hm : Complete f) (s : Finset ℕ) :
    ∑ n ∈ s, Complex.log n * f n =
      ∑ n ∈ s, ∑ p ∈ n.divisorsAntidiagonal,
        (f p.1 * (ArithmeticFunction.vonMangoldt p.1 : ℂ)) * f p.2 := by
  apply Finset.sum_congr rfl
  intro n hn
  have he := congrFun (mangoldt_convolution f hm) n
  simpa only [LSeries.convolution_def,LSeries.logMul,mangoldtTwist] using he.symm

end OrdinaryLogDerivative

end

end OAI
