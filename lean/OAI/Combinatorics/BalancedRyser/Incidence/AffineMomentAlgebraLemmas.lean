import Mathlib

namespace OAI

section

namespace Balanced.MomentAlgebra

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem centered_sum_expansion (a : ι → ℝ) (m : ℝ) :
    ∑ i, (a i - m) ^ 2 =
      (∑ i, (a i) ^ 2) - 2 * m * (∑ i, a i) +
        (Fintype.card ι : ℝ) * m ^ 2 := by
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  ring

theorem affine_centered_sum (a : ι → ℝ) (q N : ℝ) (hq : q ≠ 0)
    (hcard : (Fintype.card ι : ℝ) = q * (q + 1))
    (hfirst : ∑ i, a i = (q + 1) * N)
    (hsecond : ∑ i, (a i) ^ 2 = N ^ 2 + q * N) :
    ∑ i, (a i - N / q) ^ 2 = q * N - N ^ 2 / q := by
  rw [centered_sum_expansion, hcard, hfirst, hsecond]
  field_simp
  ring

theorem affine_variance_bound (q N : ℝ) (hq : 0 < q) :
    q * N - N ^ 2 / q ≤ q ^ 3 / 4 := by
  have hsq := sq_nonneg (N - q ^ 2 / 2)
  apply (le_div_iff₀ (show (0 : ℝ) < 4 by norm_num)).2
  apply (mul_le_mul_iff_right₀ hq).mp
  field_simp
  nlinarith

theorem affine_centered_sum_le (a : ι → ℝ) (q N : ℝ) (hq : 0 < q)
    (hcard : (Fintype.card ι : ℝ) = q * (q + 1))
    (hfirst : ∑ i, a i = (q + 1) * N)
    (hsecond : ∑ i, (a i) ^ 2 = N ^ 2 + q * N) :
    ∑ i, (a i - N / q) ^ 2 ≤ q ^ 3 / 4 := by
  rw [affine_centered_sum a q N hq.ne' hcard hfirst hsecond]
  exact affine_variance_bound q N hq

theorem directional_variance_sum {δ κ : Type*} [Fintype δ] [Fintype κ]
    (a : δ × κ → ℝ) (q N : ℝ) (hq : q ≠ 0)
    (htotal : ∑ i, (a i - N / q) ^ 2 = q * N - N ^ 2 / q) :
    ∑ d, (1 / q) * ∑ j, (a (d, j) - N / q) ^ 2 =
      N - N ^ 2 / q ^ 2 := by
  rw [← Finset.mul_sum, ← Fintype.sum_prod_type (fun i : δ × κ => (a i - N / q) ^ 2), htotal]
  field_simp

theorem directional_variance_le_count (q N : ℝ) :
    N - N ^ 2 / q ^ 2 ≤ N := by
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (sq_nonneg _))

theorem directional_variance_bounds (q N : ℝ) (hN : N ≤ q ^ 2) :
    N - N ^ 2 / q ^ 2 ≤ N ∧ N ≤ q ^ 2 :=
  ⟨directional_variance_le_count q N, hN⟩

end Balanced.MomentAlgebra

end

section

namespace Balanced.StabilityAffineArithmetic

theorem auxiliary_degree_lt_quarter {q δ d : ℝ} (hq : 100 ≤ q) (_hd : 0 ≤ d)
    (hdegree : d ^ 2 < 2 * δ) (hskew : δ < (201 / 10000 : ℝ) * q ^ 2) :
    d < q / 4 := by
  by_contra hn
  have hdn : q / 4 ≤ d := le_of_not_gt hn
  have hp := mul_nonneg (show 0 ≤ d - q / 4 by linarith)
    (show 0 ≤ d + q / 4 by linarith)
  nlinarith

theorem tangent_margin {q b δ d : ℝ} (hq : 100 ≤ q) (hb : b ≤ q) (hd : 0 ≤ d)
    (hdegree : d ^ 2 < 2 * δ) (hskew : δ < (201 / 10000 : ℝ) * q ^ 2) :
    d + 1 < (2 / 3 : ℝ) * (2 * q - b - 2 * δ / (q + 1)) := by
  have hdq := auxiliary_degree_lt_quarter hq hd hdegree hskew
  have hqpos : 0 < q + 1 := by linarith
  have hratio : 2 * δ / (q + 1) < q / 20 := by
    apply (div_lt_iff₀ hqpos).2
    nlinarith [sq_nonneg q]
  linarith

theorem degree_gap {q δ d s : ℝ} (hq : 100 ≤ q) (hd : 0 ≤ d) (hs : s ≤ d)
    (hdegree : d ^ 2 < 2 * δ) (hskew : δ < (201 / 10000 : ℝ) * q ^ 2) :
    2 * s + d < q + 1 := by
  have hdq := auxiliary_degree_lt_quarter hq hd hdegree hskew
  linarith

theorem size_lt_second_alternative {q b δ d : ℝ} (hq : 100 ≤ q)
    (hb : b ≤ q) (hd : 0 ≤ d) (hdegree : d ^ 2 < 2 * δ)
    (hskew : δ < (201 / 10000 : ℝ) * q ^ 2) :
    b < 2 * q + 1 - d := by
  have hdq := auxiliary_degree_lt_quarter hq hd hdegree hskew
  linarith

end Balanced.StabilityAffineArithmetic

end

section

namespace Balanced.StabilityArithmetic

theorem delta_pos {ζ : ℝ} (hζ : 0 < ζ) :
    0 < min (ζ / 4) (1 / 100 : ℝ) := by
  exact lt_min (by positivity) (by norm_num)

theorem hole_bound {q h Δ ζ : ℝ} (hq : 100 ≤ q)
    (hh : h < min (ζ / 4) (1 / 100 : ℝ) * q ^ 2)
    (hΔ : Δ ≤ h + q + 1) :
    Δ < (201 / 10000 : ℝ) * q ^ 2 := by
  have hmin : min (ζ / 4) (1 / 100 : ℝ) ≤ 1 / 100 := min_le_right _ _
  have hm := mul_le_mul_of_nonneg_right hmin (sq_nonneg q)
  have hfactor : 0 ≤ (q - 100) * (101 * q + 100) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem reduction_bounds {q ζ h Δ : ℝ} (hq : 100 ≤ q) (hζ : 0 < ζ)
    (hthreshold : 4 / ζ ≤ q)
    (hh : h < min (ζ / 4) (1 / 100 : ℝ) * q ^ 2)
    (hΔ : Δ ≤ h + q + 1) :
    0 < (⌊q / 3⌋ : ℝ) ∧
    q ≤ (3 / 2 : ℝ) * (q + 1) - (⌊q / 3⌋ : ℝ) ∧
    Δ < (2 / 9 : ℝ) * ((⌊q / 3⌋ : ℝ) + 1) ^ 2 ∧
    (1 - ζ) * q < q - 2 * Δ / (q + 1) := by
  have hqpos : 0 < q := by linarith
  have hqone : 0 < q + 1 := by linarith
  have hβlo : q / 3 < (⌊q / 3⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hβhi : (⌊q / 3⌋ : ℝ) ≤ q / 3 := Int.floor_le _
  have hβpos : 0 < (⌊q / 3⌋ : ℝ) := by linarith
  refine ⟨hβpos, by linarith, ?_, ?_⟩
  · have hholes := hole_bound hq hh hΔ
    have hq2 : 0 < q ^ 2 := sq_pos_of_pos hqpos
    have hprod : 0 < ((⌊q / 3⌋ : ℝ) + 1 - q / 3) *
        ((⌊q / 3⌋ : ℝ) + 1 + q / 3) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  · have hδpos := delta_pos hζ
    have hδζ : min (ζ / 4) (1 / 100 : ℝ) ≤ ζ / 4 := min_le_left _ _
    have hζq : 4 ≤ ζ * q := (div_le_iff₀ hζ).mp hthreshold |>.trans_eq (mul_comm q ζ)
    have hδq := mul_le_mul_of_nonneg_right hδζ hqpos.le
    have hratio : Δ / (q + 1) < min (ζ / 4) (1 / 100 : ℝ) * q + 1 := by
      apply (div_lt_iff₀ hqone).2
      nlinarith
    rw [mul_div_assoc]
    nlinarith

end Balanced.StabilityArithmetic

end

section

namespace Balanced.StabilityFinalArithmetic

theorem rounded_size_bound (q b d : ℕ) (β δ : ℝ)
    (hβ : 0 < β)
    (hsize : (b : ℝ) ≤ (3 / 2 : ℝ) * ((q : ℝ) + 1) - β)
    (hdegree : (d : ℝ) ^ 2 < 2 * δ)
    (hskew : δ < (2 / 9 : ℝ) * (β + 1) ^ 2) :
    2 * b + 3 * d ≤ 3 * q + 4 := by
  have hd : 3 * (d : ℝ) < 2 * (β + 1) := by
    by_contra hn
    have hn' : 2 * (β + 1) ≤ 3 * (d : ℝ) := le_of_not_gt hn
    have hprod := mul_nonneg
      (show 0 ≤ 3 * (d : ℝ) - 2 * (β + 1) by linarith)
      (show 0 ≤ 3 * (d : ℝ) + 2 * (β + 1) by positivity)
    nlinarith
  have hreal : ((2 * b + 3 * d : ℕ) : ℝ) < ((3 * q + 5 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hnat : 2 * b + 3 * d < 3 * q + 5 := by exact_mod_cast hreal
  omega

theorem collinear_lower_bound (q m n k : ℕ) (δ : ℝ)
    (hq : 1 ≤ q) (hδ : 0 ≤ δ)
    (hpartition : k + n = q + 1)
    (hsize : 2 * (m + n) + 3 * k ≤ 3 * q + 4)
    (hcount : (k : ℝ) * ((q : ℝ) - m) ≤ δ) :
    (q : ℝ) - 2 * δ / ((q : ℝ) + 1) ≤ (n : ℝ) := by
  have hqpos : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hpartR : (k : ℝ) + n = (q : ℝ) + 1 := by exact_mod_cast hpartition
  by_cases hk : k ≤ 1
  · have hqn : q ≤ n := by omega
    have hqnR : (q : ℝ) ≤ n := by exact_mod_cast hqn
    have hdiv : 0 ≤ 2 * δ / ((q : ℝ) + 1) := by positivity
    linarith
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hsmall : 2 * m + k ≤ q + 2 := by omega
  have hsmallR : 2 * (m : ℝ) + k ≤ (q : ℝ) + 2 := by exact_mod_cast hsmall
  have hmul := mul_nonneg
    (show (0 : ℝ) ≤ (k : ℝ) by positivity)
    (show (0 : ℝ) ≤ (q : ℝ) + 2 - 2 * m - k by linarith)
  have hquad := mul_nonneg
    (show (0 : ℝ) ≤ (k : ℝ) - 2 by linarith)
    (show (0 : ℝ) ≤ (k : ℝ) - 1 by linarith)
  have hscaled : ((k : ℝ) - 1) * ((q : ℝ) + 1) ≤ 2 * δ := by
    nlinarith
  have hdiv : (k : ℝ) - 1 ≤ 2 * δ / ((q : ℝ) + 1) :=
    (le_div_iff₀ hqpos).2 hscaled
  linarith

theorem collinear_lower_bound_of_source_bounds (q m n k d : ℕ) (β δ : ℝ)
    (hq : 1 ≤ q) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hpartition : k + n = q + 1) (hmissing : k ≤ d)
    (hsize : ((m + n : ℕ) : ℝ) ≤ (3 / 2 : ℝ) * ((q : ℝ) + 1) - β)
    (hdegree : (d : ℝ) ^ 2 < 2 * δ)
    (hskew : δ < (2 / 9 : ℝ) * (β + 1) ^ 2)
    (hcount : (k : ℝ) * ((q : ℝ) - m) ≤ δ) :
    (q : ℝ) - 2 * δ / ((q : ℝ) + 1) ≤ (n : ℝ) := by
  apply collinear_lower_bound q m n k δ hq hδ hpartition _ hcount
  have hs := rounded_size_bound q (m + n) d β δ hβ hsize hdegree hskew
  omega

end Balanced.StabilityFinalArithmetic

end

end OAI
