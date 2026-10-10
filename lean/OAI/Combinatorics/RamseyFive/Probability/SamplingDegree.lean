import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.RichParameters
open scoped Real

lemma exists_sampling_degree (N M q : ℕ) (hM : 0 < M) (hNM : M ≤ N)
    (hlarge : (1024 : ℝ)^2 * N ≤ (M : ℝ)^3)
    (hq : 51 * Real.sqrt ((N : ℝ) / M) < q) :
    ∃ (p : ℝ) (h : ℕ),
      0 < p ∧ p ≤ 1 ∧
      2*p*N < ((h+1)^3 : ℕ) ∧ (3*h : ℕ) ≤ p*M/2 ∧
      3*h < q ∧ 18*h < M ∧ h^2*M ≤ 289*N ∧
      p*M = 1024*Real.sqrt ((N : ℝ)/M) := by
  let r := Real.sqrt ((N : ℝ)/M)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hMnz : (M : ℝ) ≠ 0 := ne_of_gt hMpos
  have hNM' : (M : ℝ) ≤ N := by exact_mod_cast hNM
  have hr1 : 1 ≤ r := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    simpa using (le_div_iff₀ hMpos).mpr (by simpa using hNM')
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hrsq : r^2 = (N : ℝ)/M := Real.sq_sqrt (by positivity)
  have hrN : r^2*M = N := by rw [hrsq, div_mul_cancel₀ _ hMnz]
  have hrM : 1024*r ≤ M := by
    have hh : (1024*r)^2 ≤ (M : ℝ)^2 := by
      apply (mul_le_mul_iff_left₀ hMpos).mp
      nlinarith [hrN]
    nlinarith [sq_nonneg (1024*r-M)]
  let h : ℕ := ⌈16*r⌉₊
  have hhlo : 16*r ≤ (h : ℝ) := Nat.le_ceil _
  have hhhi : (h : ℝ) < 16*r+1 := Nat.ceil_lt_add_one (by positivity)
  have hh17 : (h : ℝ) < 17*r := by linarith
  refine ⟨1024*r/M, h, by positivity, (div_le_one hMpos).mpr hrM, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hN : (N : ℝ) = r^2*M := hrN.symm
    rw [hN]
    have he : 2*(1024*r/M)*(r^2*M) = 2048*r^3 := by field_simp; ring
    rw [he]
    have hr3 : 0 < r^3 := pow_pos hrpos _
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 16*r) hhlo 3
    push_cast
    nlinarith [hpow, pow_nonneg (show (0:ℝ) ≤ h by positivity) 2]
  · push_cast
    have he : (1024*r/M)*M = 1024*r := div_mul_cancel₀ _ hMnz
    rw [he]
    linarith
  · apply (Nat.cast_lt (α := ℝ)).mp
    push_cast
    dsimp [r] at hh17 ⊢
    linarith
  · apply (Nat.cast_lt (α := ℝ)).mp
    push_cast
    linarith
  · apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    have hhsq : (h : ℝ)^2 ≤ (17*r)^2 := pow_le_pow_left₀ (by positivity) hh17.le 2
    have H := mul_le_mul_of_nonneg_right hhsq hMpos.le
    nlinarith [hrN]
  · exact div_mul_cancel₀ _ hMnz
end SharpRamseyFive.RichParameters

end OAI
