import OAI.NumberTheory.TwoPointCorrelations.LocalFactors
import Mathlib.NumberTheory.Divisors

namespace OAI

/-! The general-multiplicative reduction in corrected MRT §3.  The completely
multiplicative part keeps the original values at primes; the convolution
correction vanishes at primes and is bounded by two at higher prime powers. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def mrtCompletePart (f : ℕ → ℂ) : ℕ → ℂ :=
  fromPrimePowers (fun p k => f p ^ k)

noncomputable def mrtCorrectionLocal (f : ℕ → ℂ) (p k : ℕ) : ℂ :=
  if k = 0 then 1 else f (p ^ k) - f p * f (p ^ (k - 1))

noncomputable def mrtCorrection (f : ℕ → ℂ) : ℕ → ℂ :=
  fromPrimePowers (mrtCorrectionLocal f)

lemma fromPrimePowers_prime_pow (F : ℕ → ℕ → ℂ)
    (hF : ∀ p, F p 0 = 1) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    fromPrimePowers F (p ^ k) = F p k := by
  unfold fromPrimePowers
  rw [hp.factorization_pow]
  exact Finsupp.prod_single_index (hF p)

lemma mrtCompletePart_prime_pow (f : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    mrtCompletePart f (p ^ k) = f p ^ k :=
  fromPrimePowers_prime_pow _ (fun _ => pow_zero _) hp k

lemma mrtCompletePart_mul (f : ℕ → ℂ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    mrtCompletePart f (m * n) = mrtCompletePart f m * mrtCompletePart f n := by
  unfold mrtCompletePart fromPrimePowers
  rw [Nat.factorization_mul hm.ne' hn.ne']
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

lemma mrtCompletePart_oneBounded (f : ℕ → ℂ) (hf : OneBounded f) :
    OneBounded (mrtCompletePart f) := by
  apply fromPrimePowers_oneBounded
  intro p k hp _
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (hf p hp.pos)

@[simp] lemma mrtCorrectionLocal_zero (f : ℕ → ℂ) (p : ℕ) :
    mrtCorrectionLocal f p 0 = 1 := by
  simp [mrtCorrectionLocal]

@[simp] lemma mrtCorrectionLocal_one (f : ℕ → ℂ) (h1 : f 1 = 1) (p : ℕ) :
    mrtCorrectionLocal f p 1 = 0 := by
  simp [mrtCorrectionLocal, h1]

lemma mrtCorrectionLocal_succ (f : ℕ → ℂ) (p k : ℕ) :
    mrtCorrectionLocal f p (k + 1) = f (p ^ (k + 1)) - f p * f (p ^ k) := by
  simp [mrtCorrectionLocal]

lemma mrtCorrection_prime_pow (f : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    mrtCorrection f (p ^ k) = mrtCorrectionLocal f p k :=
  fromPrimePowers_prime_pow _ (mrtCorrectionLocal_zero f) hp k

lemma mrtCorrectionLocal_norm_le (f : ℕ → ℂ) (hf : OneBounded f)
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    ‖mrtCorrectionLocal f p k‖ ≤ 2 := by
  rw [mrtCorrectionLocal, ite_eq_right hk.ne']
  apply (norm_sub_le _ _).trans
  rw [norm_mul]
  have hpow := hf (p ^ k) (pow_pos hp.pos k)
  have hprev := hf (p ^ (k - 1)) (pow_pos hp.pos (k - 1))
  have hmul := mul_le_mul (hf p hp.pos) hprev (norm_nonneg _) zero_le_one
  nlinarith

/-- The local prime-power convolution telescopes exactly. -/
lemma mrt_local_convolution (f : ℕ → ℂ) (h1 : f 1 = 1) (p k : ℕ) :
    (∑ i ∈ range (k + 1), f p ^ i * mrtCorrectionLocal f p (k - i)) =
      f (p ^ k) := by
  induction k with
  | zero => simp [h1]
  | succ k ih =>
    rw [sum_range_succ']
    simp only [pow_zero, Nat.sub_zero, one_mul, mrtCorrectionLocal_succ,
      Nat.add_sub_add_right, pow_succ']
    simp only [mul_assoc]
    rw [← mul_sum, ih]
    ring

noncomputable def mrtArithmetic (f : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else f n, by simp⟩

@[simp] lemma mrtArithmetic_apply_pos (f : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    mrtArithmetic f n = f n := ite_eq_right hn.ne'

lemma mrtArithmetic_isMultiplicative (f : ℕ → ℂ) (hf : Multiplicative f)
    (h1 : f 1 = 1) : (mrtArithmetic f).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [h1], ?_⟩
  intro m n hm hn hcop
  simp only [mrtArithmetic_apply_pos _ (Nat.pos_of_ne_zero hm),
    mrtArithmetic_apply_pos _ (Nat.pos_of_ne_zero hn),
    mrtArithmetic_apply_pos _ (Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn))]
  exact hf m n (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn) hcop

/-- Every normalized multiplicative function factors as `g₁ * h`, where
`g₁` is completely multiplicative and `h(p)=0`. -/
theorem mrt_multiplicative_convolution (f : ℕ → ℂ) (hf : Multiplicative f)
    (h1 : f 1 = 1) :
    mrtArithmetic (mrtCompletePart f) * mrtArithmetic (mrtCorrection f) =
      mrtArithmetic f := by
  have hc : (mrtArithmetic (mrtCompletePart f)).IsMultiplicative :=
    mrtArithmetic_isMultiplicative _ (fromPrimePowers_multiplicative _) (fromPrimePowers_one _)
  have hh : (mrtArithmetic (mrtCorrection f)).IsMultiplicative :=
    mrtArithmetic_isMultiplicative _ (fromPrimePowers_multiplicative _) (fromPrimePowers_one _)
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ (hc.mul hh)
    _ (mrtArithmetic_isMultiplicative f hf h1)).mpr
  intro p k hp
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
      (fun a b => mrtArithmetic (mrtCompletePart f) a * mrtArithmetic (mrtCorrection f) b),
    Nat.sum_divisors_prime_pow hp]
  calc
    _ = ∑ i ∈ range (k + 1), f p ^ i * mrtCorrectionLocal f p (k - i) := by
      apply sum_congr rfl
      intro i hi
      have hik : i ≤ k := by have := mem_range.mp hi; omega
      rw [Nat.pow_div hik hp.pos, mrtArithmetic_apply_pos _ (pow_pos hp.pos i),
        mrtArithmetic_apply_pos _ (pow_pos hp.pos (k - i)),
        mrtCompletePart_prime_pow f hp, mrtCorrection_prime_pow f hp]
    _ = _ := by rw [mrt_local_convolution f h1, mrtArithmetic_apply_pos _ (pow_pos hp.pos k)]

/-- The convolution identity in the positive-integer notation used in MRT. -/
theorem mrt_multiplicative_divisor_sum (f : ℕ → ℂ) (hf : Multiplicative f)
    (h1 : f 1 = 1) {n : ℕ} (hn : 0 < n) :
    f n = ∑ d ∈ n.divisors, mrtCorrection f d * mrtCompletePart f (n / d) := by
  have he := congrArg (fun a : ArithmeticFunction ℂ => a n)
    (mrt_multiplicative_convolution f hf h1)
  rw [mul_comm, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun a b => mrtArithmetic (mrtCorrection f) a * mrtArithmetic (mrtCompletePart f) b)] at he
  rw [mrtArithmetic_apply_pos _ hn] at he
  rw [← he]
  apply sum_congr rfl
  intro d hd
  rcases Nat.mem_divisors.mp hd with ⟨hdn, hn0⟩
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have hquot : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
  rw [mrtArithmetic_apply_pos _ hd0, mrtArithmetic_apply_pos _ hquot]

end TwoPointCorrelations

end OAI
