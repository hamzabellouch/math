import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMultiplicativeReduction
import OAI.NumberTheory.TwoPoint.Halasz.HalaszHyperbolaRows

namespace OAI

/-! The exact convolution with the constant-one function used for the
near-twist renormalization. Its prime coefficients are the actual deviation
from one, including missing-prime masks. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszUnitCorrectionLocal (F : ℕ → ℂ) (p k : ℕ) : ℂ :=
  if k = 0 then 1 else F (p ^ k) - F (p ^ (k - 1))

noncomputable def halaszUnitCorrection (F : ℕ → ℂ) : ℕ → ℂ :=
  fromPrimePowers (halaszUnitCorrectionLocal F)

@[simp] lemma halaszUnitCorrectionLocal_zero (F : ℕ → ℂ) (p : ℕ) :
    halaszUnitCorrectionLocal F p 0 = 1 := by simp [halaszUnitCorrectionLocal]

lemma halaszUnitCorrectionLocal_succ (F : ℕ → ℂ) (p k : ℕ) :
    halaszUnitCorrectionLocal F p (k + 1) = F (p ^ (k + 1)) - F (p ^ k) := by
  simp [halaszUnitCorrectionLocal]

lemma halasz_unit_correction_prime_pow (F : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    halaszUnitCorrection F (p ^ k) = halaszUnitCorrectionLocal F p k :=
  fromPrimePowers_prime_pow _ (halaszUnitCorrectionLocal_zero F) hp k

lemma halasz_unit_correction_prime (F : ℕ → ℂ) (hF : F 1 = 1)
    {p : ℕ} (hp : p.Prime) : halaszUnitCorrection F p = F p - 1 := by
  simpa [halaszUnitCorrectionLocal, hF] using halasz_unit_correction_prime_pow F hp 1

lemma halasz_unit_correction_local_sum (F : ℕ → ℂ) (hF : F 1 = 1) (p k : ℕ) :
    (∑ i ∈ range (k + 1), halaszUnitCorrectionLocal F p i) = F (p ^ k) := by
  induction k with
  | zero => simp [hF]
  | succ k ih =>
    rw [sum_range_succ, ih, halaszUnitCorrectionLocal_succ]
    ring

lemma halasz_unit_correction_convolution (F : ℕ → ℂ) (hF : Multiplicative F)
    (hF1 : F 1 = 1) :
    mrtArithmetic (halaszUnitCorrection F) * mrtArithmetic (fun _ => 1) = mrtArithmetic F := by
  have hh : (mrtArithmetic (halaszUnitCorrection F)).IsMultiplicative :=
    mrtArithmetic_isMultiplicative _ (fromPrimePowers_multiplicative _) (fromPrimePowers_one _)
  have hu : (mrtArithmetic (fun _ => (1 : ℂ))).IsMultiplicative :=
    mrtArithmetic_isMultiplicative _ (fun _ _ _ _ _ => (one_mul (1 : ℂ)).symm) rfl
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ (hh.mul hu)
    _ (mrtArithmetic_isMultiplicative F hF hF1)).mpr
  intro p k hp
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun a b => mrtArithmetic (halaszUnitCorrection F) a * mrtArithmetic (fun _ => 1) b),
    Nat.sum_divisors_prime_pow hp]
  calc
    _ = ∑ i ∈ range (k + 1), halaszUnitCorrectionLocal F p i := by
      apply sum_congr rfl
      intro i hi
      have hik : i ≤ k := by have := mem_range.mp hi; omega
      rw [mrtArithmetic_apply_pos _ (pow_pos hp.pos i), Nat.pow_div hik hp.pos,
        mrtArithmetic_apply_pos _ (pow_pos hp.pos (k - i)), mul_one,
        halasz_unit_correction_prime_pow F hp]
    _ = _ := by rw [halasz_unit_correction_local_sum F hF1,
      mrtArithmetic_apply_pos _ (pow_pos hp.pos k)]

lemma halasz_unit_correction_divisor_sum (F : ℕ → ℂ) (hF : Multiplicative F)
    (hF1 : F 1 = 1) {n : ℕ} (hn : 0 < n) :
    F n = ∑ d ∈ n.divisors, halaszUnitCorrection F d := by
  have he := congrArg (fun a : ArithmeticFunction ℂ => a n)
    (halasz_unit_correction_convolution F hF hF1)
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun a b => mrtArithmetic (halaszUnitCorrection F) a * mrtArithmetic (fun _ => 1) b),
    mrtArithmetic_apply_pos _ hn] at he
  rw [← he]
  apply sum_congr rfl
  intro d hd
  have hdn := (Nat.mem_divisors.mp hd).1
  have hd0 := Nat.pos_of_dvd_of_pos hdn hn
  have hquot : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
  rw [mrtArithmetic_apply_pos _ hd0, mrtArithmetic_apply_pos _ hquot, mul_one]

lemma halasz_unit_correction_local_bound (F : ℕ → ℂ) (hF : OneBounded F)
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    ‖halaszUnitCorrectionLocal F p k‖ ≤ 2 := by
  rw [halaszUnitCorrectionLocal, ite_eq_right hk.ne']
  exact (norm_sub_le _ _).trans (by
    linarith [hF (p ^ k) (pow_pos hp.pos k), hF (p ^ (k - 1)) (pow_pos hp.pos _)])

/-- Exact prefix hyperbola identity. -/
lemma halasz_unit_correction_prefix (F : ℕ → ℂ) (hF : Multiplicative F)
    (hF1 : F 1 = 1) (N : ℕ) :
    (∑ n ∈ Icc 1 N, F n) =
      ∑ d ∈ Icc 1 N, (N / d : ℕ) * halaszUnitCorrection F d := by
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal, halaszUnitCorrection F p.1 := by
      apply sum_congr rfl
      intro n hn
      rw [Nat.sum_divisorsAntidiagonal (fun a _ => halaszUnitCorrection F a)]
      exact halasz_unit_correction_divisor_sum F hF hF1 (mem_Icc.mp hn).1
    _ = ∑ p ∈ halaszHyperbola N, halaszUnitCorrection F p.1 :=
      halasz_sum_divisorsAntidiagonal (fun a _ => halaszUnitCorrection F a) N
    _ = _ := by
      rw [halasz_hyperbola_rows (fun a _ => halaszUnitCorrection F a) N]
      apply sum_congr rfl
      intro d _
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

end TwoPointCorrelations

end OAI
