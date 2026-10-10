import Mathlib

namespace OAI


namespace Problem355.ZeroShell

open scoped BigOperators

theorem affine_shell_sum_le {α : Type*} (S : Finset α)
    (f g len J : α → ℝ) (R I A C : ℝ)
    (hR : 0 < R) (hI : 0 < I) (hA : 0 ≤ A)
    (hg : ∀ x ∈ S, 0 < g x) (hlen : ∀ x ∈ S, R ≤ len x)
    (hJ : ∀ x ∈ S, J x = I * len x / g x)
    (hf : ∀ x ∈ S, f x ≤ A / (J x) ^ 3)
    (hmoment : ∑ x ∈ S, (g x) ^ 3 ≤ C * R ^ 3 * I) :
    ∑ x ∈ S, f x ≤ A * C / I ^ 2 := by
  have hpoint : ∀ x ∈ S, f x ≤ (A / (I ^ 3 * R ^ 3)) * (g x) ^ 3 := by
    intro x hx
    have hgx := hg x hx
    have hlx : 0 < len x := lt_of_lt_of_le hR (hlen x hx)
    have hlen3 : R ^ 3 ≤ (len x) ^ 3 := pow_le_pow_left₀ hR.le (hlen x hx) 3
    have hden : I ^ 3 * R ^ 3 ≤ I ^ 3 * (len x) ^ 3 :=
      mul_le_mul_of_nonneg_left hlen3 (pow_nonneg hI.le 3)
    calc
      f x ≤ A / (J x) ^ 3 := hf x hx
      _ = (A * (g x) ^ 3) / (I ^ 3 * (len x) ^ 3) := by
        rw [hJ x hx]
        field_simp
      _ ≤ (A * (g x) ^ 3) / (I ^ 3 * R ^ 3) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = (A / (I ^ 3 * R ^ 3)) * (g x) ^ 3 := by ring
  calc
    (∑ x ∈ S, f x) ≤ ∑ x ∈ S, (A / (I ^ 3 * R ^ 3)) * (g x) ^ 3 :=
      Finset.sum_le_sum hpoint
    _ = (A / (I ^ 3 * R ^ 3)) * ∑ x ∈ S, (g x) ^ 3 := by rw [Finset.mul_sum]
    _ ≤ (A / (I ^ 3 * R ^ 3)) * (C * R ^ 3 * I) :=
      mul_le_mul_of_nonneg_left hmoment (by positivity)
    _ = A * C / I ^ 2 := by
      field_simp

theorem uniform_shell_sum_le {α : Type*} (S : Finset α)
    (f g len J : α → ℝ) (R I A C H : ℝ)
    (hR : 0 < R) (hI : 0 < I) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hg : ∀ x ∈ S, 0 < g x) (hlen : ∀ x ∈ S, R ≤ len x)
    (hJ : ∀ x ∈ S, J x = I * len x / g x)
    (hf : ∀ x ∈ S, f x ≤ A / (J x) ^ 3)
    (hdivisor : ∀ x ∈ S, (g x) ^ 3 ≤ H * I)
    (hcard : (S.card : ℝ) ≤ C * R ^ 3) :
    ∑ x ∈ S, f x ≤ A * (C * H) / I ^ 2 := by
  apply affine_shell_sum_le S f g len J R I A (C * H) hR hI hA hg hlen hJ hf
  calc
    (∑ x ∈ S, (g x) ^ 3) ≤ ∑ _x ∈ S, H * I := Finset.sum_le_sum hdivisor
    _ = (S.card : ℝ) * (H * I) := by simp [nsmul_eq_mul]
    _ ≤ (C * R ^ 3) * (H * I) := mul_le_mul_of_nonneg_right hcard (mul_nonneg hH hI.le)
    _ = C * H * R ^ 3 * I := by ring

end Problem355.ZeroShell

end OAI
