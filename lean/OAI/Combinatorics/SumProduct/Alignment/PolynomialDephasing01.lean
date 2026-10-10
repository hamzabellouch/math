import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.WeylInverse01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
namespace PolynomialDephasing
open scoped BigOperators ComplexConjugate
open PolynomialWeyl
noncomputable section

 
theorem norm_phase_sub_one_le (t : ℝ) : ‖phase t - 1‖ ≤ 2 * Real.pi * |t| := by
  unfold phase
  rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
  have he : 2 * Real.pi * t / 2 = Real.pi * t := by ring
  rw [he, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h : |Real.sin (Real.pi * t)| ≤ |Real.pi * t| := Real.abs_sin_le_abs
  rw [abs_mul, abs_of_pos Real.pi_pos] at h
  nlinarith only [h]

theorem norm_phase_sub_le (x y : ℝ) : ‖phase x - phase y‖ ≤ 2 * Real.pi * |x - y| := by
  have he : phase x - phase y = (phase (x - y) - 1) * phase y := by
    rw [sub_mul, one_mul, ← phase_add]
    congr 2
    ring
  rw [he, norm_mul, norm_phase, mul_one]
  exact norm_phase_sub_one_le _

 
theorem monomial_phase_variation (N d : ℕ) (ε : ℝ) :
    ∑ n ∈ Finset.range (N - 1),
      ‖phase (ε * ((n + 1 : ℕ) : ℝ) ^ d) - phase (ε * (n : ℝ) ^ d)‖ ≤
        2 * Real.pi * |ε| * (N : ℝ) ^ d := by
  calc
    _ ≤ ∑ n ∈ Finset.range (N - 1),
        2 * Real.pi * |ε| * (((n + 1 : ℕ) : ℝ) ^ d - (n : ℝ) ^ d) := by
      apply Finset.sum_le_sum
      intro n _
      have h := norm_phase_sub_le (ε * ((n + 1 : ℕ) : ℝ) ^ d) (ε * (n : ℝ) ^ d)
      have hpow : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ d - (n : ℝ) ^ d :=
        sub_nonneg.mpr (pow_le_pow_left₀ (Nat.cast_nonneg n)
          (by exact_mod_cast Nat.le_succ n) d)
      rw [← mul_sub, abs_mul, abs_of_nonneg hpow] at h
      nlinarith only [h]
    _ = 2 * Real.pi * |ε| * (((N - 1 : ℕ) : ℝ) ^ d - (0 : ℝ) ^ d) := by
      rw [← Finset.mul_sum]
      congr 1
      simpa only [Nat.cast_zero] using Finset.sum_range_sub (fun n : ℕ => (n : ℝ) ^ d) (N - 1)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((N - 1 : ℕ) : ℝ))
        (show ((N - 1 : ℕ) : ℝ) ≤ N by exact_mod_cast Nat.sub_le N 1) d
      linarith [pow_nonneg (show (0 : ℝ) ≤ 0 by rfl) d]

 

theorem weighted_mean_large_prefix (N : ℕ) (hN : 0 < N)
    (f w : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (hw : ∀ n, ‖w n‖ ≤ 1)
    (V δ : ℝ) (hV : 0 ≤ V) (hδ : 0 < δ)
    (hvar : ∑ n ∈ Finset.range (N - 1), ‖w (n + 1) - w n‖ ≤ V)
    (hlarge : δ ≤ ‖mean N (fun n => w n * f n)‖) :
    ∃ M : ℕ, 0 < M ∧ M ≤ N ∧ δ * N / (1 + V) ≤ M ∧
      δ / (1 + V) ≤ ‖mean M f‖ := by
  classical
  let F : ℕ → ℂ := fun M => ∑ n ∈ Finset.range M, f n
  obtain ⟨M, hM, hmax⟩ := (Finset.Icc 1 N).exists_max_image (fun M => ‖F M‖)
    ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩⟩
  have hM₀ : 0 < M := (Finset.mem_Icc.mp hM).1
  have hMN : M ≤ N := (Finset.mem_Icc.mp hM).2
  have hbound : ‖∑ n ∈ Finset.range N, w n * f n‖ ≤ (1 + V) * ‖F M‖ := by
    have he := Finset.sum_range_by_parts w f N
    simp only [smul_eq_mul] at he
    rw [he]
    calc
      _ ≤ ‖w (N - 1) * F N‖ +
          ‖∑ n ∈ Finset.range (N - 1), (w (n + 1) - w n) * F (n + 1)‖ := norm_sub_le _ _
      _ ≤ 1 * ‖F M‖ + ∑ n ∈ Finset.range (N - 1), ‖w (n + 1) - w n‖ * ‖F M‖ := by
        apply add_le_add
        · rw [norm_mul]
          exact mul_le_mul (hw _) (hmax N (Finset.mem_Icc.mpr ⟨hN, le_rfl⟩))
            (norm_nonneg _) (by norm_num)
        · apply (norm_sum_le _ _).trans
          apply Finset.sum_le_sum
          intro n hn
          rw [norm_mul]
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact hmax (n + 1) (Finset.mem_Icc.mpr ⟨by omega,
            by have := Finset.mem_range.mp hn; omega⟩)
      _ ≤ (1 + V) * ‖F M‖ := by
        rw [← Finset.sum_mul]
        nlinarith only [mul_le_mul_of_nonneg_right hvar (norm_nonneg (F M))]
  have hsum : δ * N ≤ (1 + V) * ‖F M‖ := by
    have he : ‖mean N (fun n => w n * f n)‖ =
        ‖∑ n ∈ Finset.range N, w n * f n‖ / N := by
      simp [mean, Finset.expect_eq_sum_div_card ]
    rw [he] at hlarge
    exact ((le_div_iff₀ (Nat.cast_pos.mpr hN)).mp hlarge).trans hbound
  have hF : ‖F M‖ ≤ M := by
    apply (norm_sum_le _ _).trans
    calc
      (∑ n ∈ Finset.range M, ‖f n‖) ≤ ∑ n ∈ Finset.range M, (1 : ℝ) :=
        Finset.sum_le_sum (fun n _ => hf n)
      _ = M := by simp
  have hVM : 0 < 1 + V := by linarith
  refine ⟨M, hM₀, hMN, ?_, ?_⟩
  · apply (div_le_iff₀ hVM).mpr
    nlinarith only [hsum, hF, mul_le_mul_of_nonneg_left hF hVM.le]
  · have he : ‖mean M f‖ = ‖F M‖ / M := by
      simp [mean, F, Finset.expect_eq_sum_div_card ]
    rw [he]
    apply (div_le_div_iff₀ hVM (Nat.cast_pos.mpr hM₀)).mpr
    have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
    nlinarith only [hsum, mul_le_mul_of_nonneg_left hMN' hδ.le]

 
def fourierCoefficient {q : ℕ} [NeZero q] (F : ZMod q → ℂ) (k : ZMod q) : ℂ :=
  (q : ℂ)⁻¹ * ZMod.dft F k

theorem norm_fourierCoefficient_le_one {q : ℕ} [NeZero q]
    (F : ZMod q → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1) (k : ZMod q) :
    ‖fourierCoefficient F k‖ ≤ 1 := by
  have he : fourierCoefficient F k =
      𝔼 j : ZMod q, ZMod.stdAddChar (-(j * k)) * F j := by
    simp [fourierCoefficient, ZMod.dft_apply, Finset.expect_eq_sum_div_card, div_eq_mul_inv,
      mul_comm]
  rw [he]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply Finset.expect_le Finset.univ_nonempty
  intro j _
  simpa only [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul] using hF j

theorem fourier_expansion {q : ℕ} [NeZero q] (F : ZMod q → ℂ) (x : ZMod q) :
    F x = ∑ k : ZMod q, fourierCoefficient F k * ZMod.stdAddChar (k * x) := by
  have h := congrFun (ZMod.dft.symm_apply_apply F) x
  rw [ZMod.invDFT_apply] at h
  rw [← h]
  simp only [smul_eq_mul, Finset.mul_sum, fourierCoefficient]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem stdAddChar_int_phase {q : ℕ} [NeZero q] (z : ℤ) :
    ZMod.stdAddChar (z : ZMod q) = phase ((z : ℝ) / q) := by
  rw [ZMod.stdAddChar_coe, phase]
  congr 1
  push_cast
  ring

theorem stdAddChar_mul_nat_phase {q : ℕ} [NeZero q] (k : ZMod q) (n : ℕ) :
    ZMod.stdAddChar (k * (n : ZMod q)) = phase ((k.val : ℝ) / q * n) := by
  have he : (((k.val : ℤ) * n : ℤ) : ZMod q) = k * (n : ZMod q) := by simp
  rw [← he, stdAddChar_int_phase]
  congr 1
  push_cast
  ring

theorem rational_monomial_phase {q : ℕ} [NeZero q] (m : ℤ) (d n : ℕ) :
    phase ((m : ℝ) / q * (n : ℝ) ^ d) =
      ZMod.stdAddChar ((m : ZMod q) * (n : ZMod q) ^ d) := by
  have he : ((m * (n : ℤ) ^ d : ℤ) : ZMod q) =
      (m : ZMod q) * (n : ZMod q) ^ d := by push_cast; rfl
  rw [← he, stdAddChar_int_phase]
  congr 1
  push_cast
  ring

 

theorem periodic_weight_large_frequency {q : ℕ} [NeZero q]
    (F : ZMod q → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1) (f : ℕ → ℂ)
    (N : ℕ) (δ : ℝ) (hlarge : δ ≤ ‖mean N (fun n => F (n : ZMod q) * f n)‖) :
    ∃ k : ZMod q, δ / q ≤
      ‖mean N (fun n => ZMod.stdAddChar (k * (n : ZMod q)) * f n)‖ := by
  classical
  let G := fun k : ZMod q => mean N (fun n => ZMod.stdAddChar (k * (n : ZMod q)) * f n)
  have he : mean N (fun n => F (n : ZMod q) * f n) =
      ∑ k : ZMod q, fourierCoefficient F k * G k := by
    unfold mean
    conv_lhs => arg 2; ext n; dsimp only; rw [fourier_expansion F (n : ZMod q)]
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [Finset.expect_sum_comm]
    simp_rw [← Finset.mul_expect]
    rfl
  obtain ⟨k, _, hmax⟩ := Finset.univ.exists_max_image (fun k : ZMod q => ‖G k‖)
    Finset.univ_nonempty
  refine ⟨k, ?_⟩
  have hbound : δ ≤ (q : ℝ) * ‖G k‖ := by
    apply hlarge.trans
    rw [he]
    apply (norm_sum_le _ _).trans
    calc
      (∑ j : ZMod q, ‖fourierCoefficient F j * G j‖) ≤ ∑ _j : ZMod q, ‖G k‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        exact (mul_le_mul (norm_fourierCoefficient_le_one F hF j)
          (hmax j (Finset.mem_univ j)) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      _ = (q : ℝ) * ‖G k‖ := by simp
  apply (div_le_iff₀ (show 0 < (q : ℝ) by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q))).mpr
  nlinarith only [hbound]

 

theorem remove_rational_monomial (q B N d : ℕ) (hq : 0 < q) (hqB : q ≤ B)
    (hN : 0 < N) (m : ℤ) (ε A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ)
    (hε : |ε| * (N : ℝ) ^ d ≤ A) (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hlarge : δ ≤ ‖mean N (fun n =>
      phase ((m : ℝ) / q * (n : ℝ) ^ d) * phase (ε * (n : ℝ) ^ d) * f n)‖) :
    ∃ l : ℕ, l < q ∧ ∃ M : ℕ, 0 < M ∧ M ≤ N ∧
      δ / ((B : ℝ) * (1 + 2 * Real.pi * A)) * N ≤ M ∧
      δ / ((B : ℝ) * (1 + 2 * Real.pi * A)) ≤
        ‖mean M (fun n => phase ((l : ℝ) / q * n) * f n)‖ := by
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  let F : ZMod q → ℂ := fun x => ZMod.stdAddChar ((m : ZMod q) * x ^ d)
  have hlarge' : δ ≤ ‖mean N (fun n =>
      F (n : ZMod q) * (phase (ε * (n : ℝ) ^ d) * f n))‖ := by
    simpa only [F, ← rational_monomial_phase, mul_assoc] using hlarge
  obtain ⟨k, hk⟩ := periodic_weight_large_frequency F
    (fun x => by simp [F, ZMod.stdAddChar_apply, Circle.norm_coe])
    (fun n => phase (ε * (n : ℝ) ^ d) * f n) N δ hlarge'
  have hk' : δ / q ≤ ‖mean N (fun n => phase (ε * (n : ℝ) ^ d) *
      (phase ((k.val : ℝ) / q * n) * f n))‖ := by
    simpa only [stdAddChar_mul_nat_phase, mul_left_comm] using hk
  obtain ⟨M, hM, hMN, hlength, hmean⟩ := weighted_mean_large_prefix N hN
    (fun n => phase ((k.val : ℝ) / q * n) * f n)
    (fun n => phase (ε * (n : ℝ) ^ d))
    (fun n => by simpa only [norm_mul, norm_phase, one_mul] using hf n)
    (fun n => by simp) (2 * Real.pi * A) (δ / q) (by positivity) (by positivity)
    (by
      apply (monomial_phase_variation N d ε).trans
      have h := mul_le_mul_of_nonneg_left hε (by positivity : 0 ≤ 2 * Real.pi)
      nlinarith only [h]) hk'
  have hq₀ : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hB₀ : 0 < (B : ℝ) := Nat.cast_pos.mpr (hq.trans_le hqB)
  have hden : 0 < 1 + 2 * Real.pi * A := by positivity
  have hweak : δ / ((B : ℝ) * (1 + 2 * Real.pi * A)) ≤
      (δ / q) / (1 + 2 * Real.pi * A) := by
    rw [div_div]
    apply div_le_div_of_nonneg_left hδ.le (by positivity)
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hqB) hden.le
  refine ⟨k.val, ZMod.val_lt k, M, hM, hMN, ?_, hweak.trans hmean⟩
  have he : (δ / q) * N / (1 + 2 * Real.pi * A) =
      ((δ / q) / (1 + 2 * Real.pi * A)) * N := by ring
  rw [he] at hlength
  exact (mul_le_mul_of_nonneg_right hweak (Nat.cast_nonneg N)).trans hlength

end
end PolynomialDephasing

namespace WeylCoefficients
open scoped BigOperators ComplexConjugate
open PolynomialWeyl PolynomialDephasing WeylInverse
noncomputable section

 

def lowerWithFrequency (p : Polynomial ℝ) (d l q : ℕ) : Polynomial ℝ :=
  p.erase (d + 1) + Polynomial.monomial 1 ((l : ℝ) / q)

theorem lowerWithFrequency_degree (p : Polynomial ℝ) (d l q : ℕ)
    (hd : 0 < d) (hp : p.natDegree ≤ d + 1) :
    (lowerWithFrequency p d l q).natDegree ≤ d := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    by_cases he : j = d + 1
    · simp [he]
    · rw [Polynomial.erase_ne p he]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · exact (Polynomial.natDegree_monomial_le _).trans hd

theorem lowerWithFrequency_coeff (p : Polynomial ℝ) (d l q j : ℕ) (hj : j ≤ d) :
    (lowerWithFrequency p d l q).coeff j = p.coeff j + if j = 1 then (l : ℝ) / q else 0 := by
  simp only [lowerWithFrequency, Polynomial.coeff_add,
    Polynomial.erase_ne p (show j ≠ d + 1 by omega), Polynomial.coeff_monomial]
  by_cases he : j = 1 <;> simp [he, eq_comm]

 

theorem remove_leading_coefficient (d A N q : ℕ) (_hA : 0 < A) (hN : 0 < N)
    (hq : 0 < q) (hqA : q ≤ A) (p : Polynomial ℝ) (m : ℤ) (δ : ℝ) (hδ : 0 < δ)
    (hm : |(q : ℝ) * p.coeff (d + 1) - m| ≤ (A : ℝ) / (N : ℝ) ^ (d + 1))
    (hlarge : δ ≤ ‖mean N (polynomialPhase p)‖) :
    ∃ l : ℕ, l < q ∧ ∃ M : ℕ, 0 < M ∧ M ≤ N ∧
      δ / ((A : ℝ) * (1 + 2 * Real.pi * A)) * N ≤ M ∧
      δ / ((A : ℝ) * (1 + 2 * Real.pi * A)) ≤
        ‖mean M (polynomialPhase (lowerWithFrequency p d l q))‖ := by
  let ε := p.coeff (d + 1) - (m : ℝ) / q
  have hq₀ : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hq₁ : 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have hεeq : (q : ℝ) * ε = (q : ℝ) * p.coeff (d + 1) - m := by
    dsimp [ε]
    field_simp
  have hε : |ε| * (N : ℝ) ^ (d + 1) ≤ A := by
    apply (le_div_iff₀ (pow_pos (Nat.cast_pos.mpr hN) _)).mp
    apply le_trans _ hm
    rw [← hεeq, abs_mul, abs_of_pos hq₀]
    have h := mul_le_mul_of_nonneg_right hq₁ (abs_nonneg ε)
    simpa only [one_mul] using h
  have he (n : ℕ) : p.eval (n : ℝ) =
      (m : ℝ) / q * (n : ℝ) ^ (d + 1) + ε * (n : ℝ) ^ (d + 1) +
      (p.erase (d + 1)).eval (n : ℝ) := by
    have h := congrArg (fun u : Polynomial ℝ => u.eval (n : ℝ)) (p.monomial_add_erase (d + 1))
    simp only [Polynomial.eval_add, Polynomial.eval_monomial] at h
    dsimp [ε]
    linarith only [h]
  obtain ⟨l, hl, M, hM, hMN, hlength, hmean⟩ := remove_rational_monomial q A N (d + 1)
    hq hqA hN m ε A δ (Nat.cast_nonneg _) hδ hε (polynomialPhase (p.erase (d + 1)))
    (fun n => by simp [polynomialPhase]) (by
      change δ ≤ ‖mean N (fun n => phase (p.eval (n : ℝ)))‖ at hlarge
      simp_rw [he, phase_add] at hlarge
      exact hlarge)
  refine ⟨l, hl, M, hM, hMN, hlength, ?_⟩
  have hfun : polynomialPhase (lowerWithFrequency p d l q) =
      (fun n : ℕ => phase ((l : ℝ) / q * (n : ℝ)) * polynomialPhase (p.erase (d + 1)) n) := by
    funext n
    simp [polynomialPhase, lowerWithFrequency, Polynomial.eval_add,
      Polynomial.eval_monomial, phase_add, mul_comm]
  rw [hfun]
  exact hmean

 

theorem prefix_error_transfer (N M T d j : ℕ) (hN : 0 < N) (hM : 0 < M)
    (hT : 1 ≤ T) (hj : j ≤ d) (hNM : (N : ℝ) ≤ (T : ℝ) * M)
    (C : ℝ) (hC : 0 ≤ C) :
    C / (M : ℝ) ^ j ≤ C * (T : ℝ) ^ d / (N : ℝ) ^ j := by
  apply (div_le_div_iff₀ (pow_pos (Nat.cast_pos.mpr hM) _)
    (pow_pos (Nat.cast_pos.mpr hN) _)).mpr
  have hpow : (N : ℝ) ^ j ≤ (T : ℝ) ^ d * (M : ℝ) ^ j := by
    calc
      _ ≤ ((T : ℝ) * M) ^ j := pow_le_pow_left₀ (Nat.cast_nonneg _) hNM _
      _ = (T : ℝ) ^ j * (M : ℝ) ^ j := mul_pow ..
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by exact_mod_cast hT) hj)
        (by positivity)
  have h := mul_le_mul_of_nonneg_left hpow hC
  nlinarith only [h]

 

def CoefficientInverse (d : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ A : ℕ, 0 < A ∧
    ∀ N : ℕ, 0 < N → ∀ p : Polynomial ℝ, p.natDegree ≤ d →
      δ ≤ ‖mean N (polynomialPhase p)‖ →
      ∃ q : ℕ, 0 < q ∧ q ≤ A ∧ ∃ m : ℕ → ℤ,
        ∀ j : ℕ, 0 < j → j ≤ d →
          |(q : ℝ) * p.coeff j - m j| ≤ (A : ℝ) / (N : ℝ) ^ j

theorem coefficient_inverse_zero : CoefficientInverse 0 := by
  intro δ _
  refine ⟨1, by omega, ?_⟩
  intro N _ p _ _
  exact ⟨1, by omega, le_rfl, fun _ => 0, fun j hj hj' => by omega⟩

theorem coefficient_inverse_one : CoefficientInverse 1 := by
  intro δ hδ
  obtain ⟨A, hA, hinv⟩ := leading_inverse_one δ hδ
  refine ⟨A, hA, ?_⟩
  intro N hN p hp hlarge
  obtain ⟨q, hq, hqA, m, hm⟩ := hinv N hN p hp hlarge
  refine ⟨q, hq, hqA, fun _ => m, ?_⟩
  intro j hj hj'
  have : j = 1 := by omega
  subst j
  exact hm

 

theorem coefficient_inverse_succ (d : ℕ) (hd : 0 < d)
    (ih : CoefficientInverse d) : CoefficientInverse (d + 1) := by
  intro δ hδ
  obtain ⟨A, hA, hlead⟩ := leading_inverse (d + 1) (by omega) δ hδ
  let τ := δ / ((A : ℝ) * (1 + 2 * Real.pi * A))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨A', hA', hlower⟩ := ih τ hτ
  obtain ⟨T, hT⟩ := exists_nat_gt (max (1 : ℝ) (1 / τ))
  have hT₁ : 1 ≤ (T : ℝ) := (le_max_left _ _).trans hT.le
  have hTnat : 1 ≤ T := by exact_mod_cast hT₁
  have hTτ : 1 ≤ (T : ℝ) * τ :=
    (div_le_iff₀ hτ).mp ((le_max_right _ _).trans hT.le)
  let C := A * A'
  let B := C * T ^ d + C + 1
  have hB : 0 < B := by dsimp [B]; omega
  have hCB : C ≤ B := by dsimp [B]; omega
  have hCTB : C * T ^ d ≤ B := by dsimp [B]; omega
  refine ⟨B, hB, ?_⟩
  intro N hN p hp hlarge
  obtain ⟨q, hq, hqA, m, hm⟩ := hlead N hN p hp hlarge
  obtain ⟨l, _, M, hM, _, hlength, hmean⟩ := remove_leading_coefficient d A N q
    hA hN hq hqA p m δ hδ hm hlarge
  obtain ⟨b, hb, hbA', z, hz⟩ := hlower M hM (lowerWithFrequency p d l q)
    (lowerWithFrequency_degree p d l q hd hp) hmean
  have hNM : (N : ℝ) ≤ (T : ℝ) * M := by
    change τ * N ≤ (M : ℝ) at hlength
    have h₁ := mul_le_mul_of_nonneg_right hTτ (Nat.cast_nonneg N)
    have h₂ := mul_le_mul_of_nonneg_left hlength (Nat.cast_nonneg T)
    nlinarith only [h₁, h₂]
  let z' : ℕ → ℤ := fun j => if j = d + 1 then (b : ℤ) * m else
    (q : ℤ) * z j - if j = 1 then (b : ℤ) * l else 0
  refine ⟨q * b, by positivity, (Nat.mul_le_mul hqA hbA').trans hCB, z', ?_⟩
  intro j hj hjd
  have hN₀ : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hM₀ : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hq₀ : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hb₀ : 0 < (b : ℝ) := Nat.cast_pos.mpr hb
  have hCB' : (C : ℝ) ≤ B := by exact_mod_cast hCB
  by_cases hjtop : j = d + 1
  · subst j
    have he : ((q * b : ℕ) : ℝ) * p.coeff (d + 1) - (z' (d + 1) : ℝ) =
        (b : ℝ) * ((q : ℝ) * p.coeff (d + 1) - m) := by
      simp only [z', ite_eq_left rfl, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
      ring
    rw [he, abs_mul, abs_of_pos hb₀]
    calc
      _ ≤ (b : ℝ) * ((A : ℝ) / (N : ℝ) ^ (d + 1)) :=
        mul_le_mul_of_nonneg_left hm hb₀.le
      _ ≤ (C : ℝ) / (N : ℝ) ^ (d + 1) := by
        rw [← mul_div_assoc]
        apply div_le_div_of_nonneg_right _ (by positivity)
        have h := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hbA' : (b : ℝ) ≤ A')
          (Nat.cast_nonneg A)
        simp only [C, Nat.cast_mul]
        nlinarith only [h]
      _ ≤ _ := div_le_div_of_nonneg_right hCB' (by positivity)
  · have hjd' : j ≤ d := by omega
    have he : ((q * b : ℕ) : ℝ) * p.coeff j - (z' j : ℝ) =
        (q : ℝ) * ((b : ℝ) * (lowerWithFrequency p d l q).coeff j - z j) := by
      rw [lowerWithFrequency_coeff p d l q j hjd']
      by_cases hjone : j = 1
      · simp only [z', ite_eq_right hjtop, ite_eq_left hjone, Int.cast_sub, Int.cast_mul,
          Int.cast_natCast, Nat.cast_mul]
        field_simp
        ring
      · simp only [z', ite_eq_right hjtop, ite_eq_right hjone, Int.cast_mul,
          Int.cast_natCast, Nat.cast_mul, sub_zero, add_zero]
        ring
    rw [he, abs_mul, abs_of_pos hq₀]
    calc
      _ ≤ (q : ℝ) * ((A' : ℝ) / (M : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_left (hz j hj hjd') hq₀.le
      _ ≤ (C : ℝ) / (M : ℝ) ^ j := by
        rw [← mul_div_assoc]
        apply div_le_div_of_nonneg_right _ (by positivity)
        have h := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hqA : (q : ℝ) ≤ A)
          (Nat.cast_nonneg A')
        simpa only [C, Nat.cast_mul] using h
      _ ≤ (C : ℝ) * (T : ℝ) ^ d / (N : ℝ) ^ j :=
        prefix_error_transfer N M T d j hN hM hTnat hjd' hNM C (Nat.cast_nonneg _)
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast hCTB

 

theorem coefficient_inverse (d : ℕ) : CoefficientInverse d := by
  induction d with
  | zero => exact coefficient_inverse_zero
  | succ d ih =>
    by_cases hd : d = 0
    · subst d
      exact coefficient_inverse_one
    · exact coefficient_inverse_succ d (Nat.pos_of_ne_zero hd) ih

end
end WeylCoefficients

end
end
end
end

end OAI
