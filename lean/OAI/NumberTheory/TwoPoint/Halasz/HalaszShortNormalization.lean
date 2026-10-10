import OAI.NumberTheory.TwoPoint.PublishedInputs

namespace OAI

/-! The allowed zero multiplicative function causes no normalization
restriction in the short-sum estimates. -/

namespace TwoPointCorrelations

open Finset

lemma Multiplicative.one_zero_or_one {F : ℕ → ℂ} (hF : Multiplicative F) :
    F 1 = 0 ∨ F 1 = 1 := by
  apply eq_zero_or_one_of_sq_eq_self
  simpa only [pow_two,one_mul] using
    (hF 1 1 Nat.one_pos Nat.one_pos (by decide)).symm

lemma Multiplicative.zero_of_one_zero {F : ℕ → ℂ} (hF : Multiplicative F)
    (hF1 : F 1 = 0) {n : ℕ} (hn : 0 < n) : F n = 0 := by
  have hh := hF 1 n Nat.one_pos hn (Nat.coprime_one_left n)
  simpa only [one_mul,hF1,zero_mul] using hh

lemma shortExponentialSum_of_one_zero {F : ℕ → ℂ} (hF : Multiplicative F)
    (hF1 : F 1 = 0) (H : ℕ) (α x : ℝ) :
    shortExponentialSum F H α x = 0 := by
  unfold shortExponentialSum
  apply sum_eq_zero
  intro n hn
  have hp : 0 < n := by have hh := (mem_Icc.mp hn).1; omega
  rw [hF.zero_of_one_zero hF1 hp,zero_mul]

lemma shortExponentialIntegral_of_one_zero {F : ℕ → ℂ} (hF : Multiplicative F)
    (hF1 : F 1 = 0) (X H : ℕ) (α : ℝ) :
    shortExponentialIntegral F X H α = 0 := by
  unfold shortExponentialIntegral
  simp only [shortExponentialSum_of_one_zero hF hF1,norm_zero,
    intervalIntegral.integral_zero]

end TwoPointCorrelations

end OAI
