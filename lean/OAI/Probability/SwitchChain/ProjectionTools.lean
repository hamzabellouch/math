import Mathlib

namespace OAI

namespace Problem315
namespace ProjectionTools

open scoped BigOperators

theorem rankOne_plane_bound (x y ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    -(x ^ 2 + y ^ 2) * (1 - ρ ^ 2) ≤
      2 * x * y * ρ * (1 - ρ ^ 2) := by
  have hfac : 0 ≤ 1 - ρ ^ 2 := by nlinarith
  have hbase : -(x ^ 2 + y ^ 2) ≤ 2 * x * y * ρ := by
    have hplus := sq_nonneg (x + y)
    have hminus := sq_nonneg (x - y)
    have hleft := mul_nonneg hρ0 hplus
    have hright := mul_nonneg (sub_nonneg.mpr hρ1) (add_nonneg (sq_nonneg x) (sq_nonneg y))
    nlinarith
  exact mul_le_mul_of_nonneg_right hbase hfac

theorem sum_disjoint_nonneg {ι : Type*} [DecidableEq ι]
    (s : Finset (ι × ι)) (cross gain err : ι → ι → ℝ)
    (hsymm : ∀ p ∈ s, p.swap ∈ s)
    (hlocal : ∀ a b, (a,b) ∈ s →
      2 * gain a b - err a b - err b a ≤ 2 * cross a b)
    (hbudget : (∑ p ∈ s, err p.1 p.2) ≤ ∑ p ∈ s, gain p.1 p.2) :
    0 ≤ ∑ p ∈ s, cross p.1 p.2 := by
  have hswap : (∑ p ∈ s, err p.2 p.1) = ∑ p ∈ s, err p.1 p.2 := by
    apply Finset.sum_bij (fun p _ => p.swap)
    · intro p hp
      exact hsymm p hp
    · intro p hp q hq hpq
      exact Prod.swap_injective hpq
    · intro p hp
      exact ⟨p.swap, hsymm p hp, Prod.swap_swap p⟩
    · intro p hp
      rfl
  have hsum := Finset.sum_le_sum (s := s) (fun p hp => hlocal p.1 p.2 hp)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  rw [hswap] at hsum
  linarith

theorem slice_numerator_bound (N q r : ℝ) (hN : 3 ≤ N)
    (hq : 1 ≤ q) (hr : 1 ≤ r) (hsum : q + r = N) :
    (2 * q - N) ^ 2 * (N - 1) ≤
      (N - 2) * (q * (q - 1) + r * (r - 1)) := by
  have hqr : N - 1 ≤ q * r := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hr)]
  have hprod : 0 ≤ 2 * N * (q * r - (N - 1)) :=
    mul_nonneg (by linarith) (by linarith)
  rw [← hsum] at hprod ⊢
  nlinarith

theorem slice_mu_one_le (N q r : ℝ) (hN : 3 ≤ N)
    (hq : 1 ≤ q) (hr : 1 ≤ r) (hsum : q + r = N) :
    (2 * q - N) ^ 2 /
      (2 * (N - 2) * ((q * (q - 1) + r * (r - 1)) / (N * (N - 1)))) ≤
      N / 2 := by
  have hN0 : 0 < N := by linarith
  have hN1 : 0 < N - 1 := by linarith
  have hN2 : 0 < N - 2 := by linarith
  have hnum : 0 < q * (q - 1) + r * (r - 1) := by
    nlinarith [sq_nonneg (q - 1), sq_nonneg (r - 1)]
  have hp : 0 < (q * (q - 1) + r * (r - 1)) / (N * (N - 1)) :=
    div_pos hnum (mul_pos hN0 hN1)
  apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num) hN2) hp)).mpr
  have hb := slice_numerator_bound N q r hN hq hr hsum
  apply (mul_le_mul_iff_of_pos_right (mul_pos hN0 hN1)).mp
  field_simp
  nlinarith [mul_nonneg (le_of_lt hN0) (sub_nonneg.mpr hb)]

theorem slice_mu_two_le (N μ : ℝ) (hN : 4 ≤ N)
    (htrace : (N * (N - 1) / 2 - N) * μ ≤ N * (N - 1) / 2) :
    μ ≤ N - 1 := by
  have hNpos : 0 < N := by linarith
  have hdim : 0 < N * (N - 1) / 2 - N := by nlinarith
  have hpoly : N * (N - 1) / 2 ≤
      (N * (N - 1) / 2 - N) * (N - 1) := by
    have hfactor := mul_nonneg (mul_nonneg (le_of_lt hNpos) (by linarith : 0 ≤ N - 1))
      (by linarith : 0 ≤ N - 4)
    nlinarith
  exact (mul_le_mul_iff_of_pos_left hdim).mp (htrace.trans hpoly)

theorem disjoint_event_correlation (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hpq : p + q < 1) :
    0 < Real.sqrt (p * q / ((1 - p) * (1 - q))) ∧
      Real.sqrt (p * q / ((1 - p) * (1 - q))) < 1 := by
  have hp1 : 0 < 1 - p := by linarith
  have hq1 : 0 < 1 - q := by linarith
  have hden : 0 < (1 - p) * (1 - q) := mul_pos hp1 hq1
  have hratio : 0 < p * q / ((1 - p) * (1 - q)) := div_pos (mul_pos hp hq) hden
  constructor
  · exact Real.sqrt_pos.mpr hratio
  · apply (Real.sqrt_lt (le_of_lt hratio) (by norm_num : (0 : ℝ) ≤ 1)).mpr
    apply (div_lt_iff₀ hden).mpr
    nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open scoped RealInnerProductSpace

theorem inner_error_bound (a b : E) :
    -(‖a‖ ^ 2 + ‖b‖ ^ 2) ≤ 2 * ⟪a, b⟫ := by
  have h : 0 ≤ ⟪a + b, a + b⟫ := real_inner_self_nonneg
  simp only [inner_add_left, inner_add_right, real_inner_self_eq_norm_sq,
    real_inner_comm b a] at h
  rw [real_inner_comm a b] at h
  linarith

theorem interaction_of_orthogonal_decomposition (z a b g ra rb : E)
    (hza : ⟪z, a⟫ = 0) (hzb : ⟪z, b⟫ = 0)
    (hg : ‖g‖ ≤ ‖z‖) (ha : ‖a‖ ≤ ‖ra‖) (hb : ‖b‖ ≤ ‖rb‖) :
    2 * ‖g‖ ^ 2 - ‖ra‖ ^ 2 - ‖rb‖ ^ 2 ≤
      2 * ⟪z + a, z + b⟫ := by
  have hga : ‖g‖ ^ 2 ≤ ‖z‖ ^ 2 := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hg
  have haa : ‖a‖ ^ 2 ≤ ‖ra‖ ^ 2 := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr ha
  have hbb : ‖b‖ ^ 2 ≤ ‖rb‖ ^ 2 := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hb
  have hab := inner_error_bound a b
  have haz : ⟪a, z⟫ = 0 := by rw [real_inner_comm, hza]
  simp only [inner_add_left, inner_add_right, real_inner_self_eq_norm_sq,
    hzb, haz, add_zero, zero_add]
  linarith

end ProjectionTools
end Problem315

end OAI
