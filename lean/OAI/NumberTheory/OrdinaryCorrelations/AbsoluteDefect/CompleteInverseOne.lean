import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OneOrZero

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

namespace OrdinaryCorrelations.Completion
open ArithmeticFunction Finset

@[simp] lemma completeInverse_one (f : ℕ → ℂ) : completeInverse f 1 = 1 := by
  simp [completeInverse]

@[simp] lemma completeInverse_prime (f : ℕ → ℂ) {p : ℕ} (hp : Nat.Prime p) :
    completeInverse f p = -f p := by
  simp [completeInverse,complete_prime f hp,ArithmeticFunction.moebius_apply_prime hp]

lemma completeInverse_prime_pow (f : ℕ → ℂ) {p : ℕ} (hp : Nat.Prime p) (k : ℕ) :
    completeInverse f (p^(k+2)) = 0 := by
  have hk : k+2 ≠ 0 := by omega
  have hk1 : k+2 ≠ 1 := by omega
  simp [completeInverse,ArithmeticFunction.moebius_apply_prime_pow hp hk,hk1]

lemma kernel_prime_pow (f : ℕ → ℂ) {p : ℕ} (hp : Nat.Prime p) (k : ℕ) :
    kernel f (p^(k+1)) = f (p^(k+1)) - f p * f (p^k) := by
  unfold kernel
  rw [mul_comm,mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => completeInverse f a * arithmetic f b),
    Nat.sum_divisors_prime_pow hp]
  rw [Finset.sum_range_succ',Finset.sum_range_succ']
  have hs : (∑ i ∈ range k,
      completeInverse f (p^(i+1+1)) * arithmetic f (p^(k+1) / p^(i+1+1))) = 0 := by
    apply sum_eq_zero
    intro i hi
    simp [show i+1+1=i+2 by omega,completeInverse_prime_pow f hp]
  rw [hs]
  simp only [zero_add,pow_zero,pow_one,completeInverse_one,one_mul,Nat.div_one,
    completeInverse_prime f hp,arithmetic_apply_pos f (pow_ne_zero _ hp.ne_zero)]
  rw [pow_succ,Nat.mul_div_cancel _ hp.pos,
    arithmetic_apply_pos f (pow_ne_zero _ hp.ne_zero)]
  rw [←pow_succ]
  ring

lemma kernel_prime {f : ℕ → ℂ} (h1 : f 1 = 1) {p : ℕ} (hp : Nat.Prime p) :
    kernel f p = 0 := by
  simpa [h1] using kernel_prime_pow f hp 0

lemma kernel_prime_pow_norm {f : ℕ → ℂ} (hf : OneBounded f) {p : ℕ}
    (hp : Nat.Prime p) (k : ℕ) : ‖kernel f (p^(k+1))‖ ≤ 2 := by
  rw [kernel_prime_pow f hp]
  calc
    ‖f (p^(k+1))-f p*f (p^k)‖ ≤ ‖f (p^(k+1))‖+‖f p*f (p^k)‖ := norm_sub_le _ _
    _ ≤ 1+1 := add_le_add (hf _) (by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hf _) (norm_nonneg _)).trans (by simpa using hf (p^k)))
    _ = 2 := by norm_num

lemma kernel_one_norm {f : ℕ → ℂ} (h1 : f 1 = 1) : ‖kernel f 1‖ = 1 := by
  simp [kernel,h1]

theorem decomposition (f : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    f n = ∑ d ∈ n.divisors, kernel f d * complete f (n/d) := by
  have he := congrArg (fun a : ArithmeticFunction ℂ => a n) (kernel_reconstruct f)
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => kernel f a * complete f b),
    arithmetic_apply_pos f hn] at he
  exact he.symm

lemma kernel_vanishes_if_squarefree_factor {f : ℕ → ℂ} (hf : Multiplicative f)
    (h1 : f 1 = 1) {n p : ℕ} (hp : Nat.Prime p) (_hn : n ≠ 0)
    (hpn : p ∣ n) (hp2 : ¬ p^2 ∣ n) : kernel f n = 0 := by
  have hfac : n = p*(n/p) := (Nat.mul_div_cancel' hpn).symm
  have hc : p.Coprime (n/p) := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    apply hp2
    rw [hfac,pow_two]
    exact mul_dvd_mul_left p hd
  rw [hfac, (kernel_multiplicative hf h1).map_mul_of_coprime hc,kernel_prime h1 hp,zero_mul]

end OrdinaryCorrelations.Completion

end

end OAI
