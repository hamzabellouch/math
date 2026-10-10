import Mathlib

namespace OAI

open scoped Classical

namespace ThorpCompatibility
open Finset

lemma sum_reverse_succ (n : ℕ) (f : ℕ → ℝ) :
    (∑ t : Fin n, f (n - (t : ℕ))) = ∑ t : Fin n, f ((t : ℕ) + 1) := by
  apply Fintype.sum_equiv Fin.revPerm
  intro t
  congr 1
  change n - (t : ℕ) = n - ((t : ℕ) + 1) + 1
  omega

lemma sum_log_sub (n : ℕ) :
    (∑ t : Fin n, Real.log ((n - (t : ℕ) : ℕ) : ℝ)) = Real.log (n.factorial : ℝ) := by
  rw [sum_reverse_succ n (fun k => Real.log (k : ℝ)),
    Fin.sum_univ_eq_sum_range (fun k => Real.log ((k + 1 : ℕ) : ℝ)),
    Nat.factorial_eq_prod_range_add_one, Nat.cast_prod]
  exact (Real.log_prod (fun i _ => by positivity)).symm

lemma sum_inv_sub (n : ℕ) :
    (∑ t : Fin n, 1 / ((n - (t : ℕ) : ℕ) : ℝ)) = (harmonic n : ℝ) := by
  rw [sum_reverse_succ n (fun k => 1 / (k : ℝ)),
    Fin.sum_univ_eq_sum_range (fun k => 1 / ((k + 1 : ℕ) : ℝ))]
  simp [harmonic, one_div]

lemma log_step_lower {x : ℝ} (hx : 0 < x) :
    Real.log x + 1 ≤ (x + 1) * Real.log (x + 1) - x * Real.log x := by
  have hx1 : 0 < x + 1 := by linarith
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hx hx1)) hx1.le
  rw [Real.log_div hx.ne' hx1.ne'] at h
  have hr : (x + 1) * (x / (x + 1) - 1) = -1 := by field_simp; ring
  rw [hr] at h
  nlinarith

lemma log_factorial_upper (n : ℕ) (hn : 0 < n) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n - n + 1 + Real.log n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      norm_num
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    have h₁ := ih hnpos
    have h₂ := log_step_lower hnreal
    rw [Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    simp only [Nat.cast_succ]
    linarith

lemma neg_log_add_lower {b a : ℝ} (hb : 0 < b) (ha : 0 ≤ a) :
    -Real.log b - a / b ≤ -Real.log (b + a) := by
  have hba : 0 < b + a := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hba hb)
  rw [Real.log_div hba.ne' hb.ne'] at h
  have hr : (b + a) / b - 1 = a / b := by field_simp; ring
  rw [hr] at h
  linarith

lemma average_log_rank_lower {D : ℕ} (hD : 0 < D) :
    1 - (1 + Real.log (D : ℝ)) / (D : ℝ) ≤
      (∑ t : Fin D, -Real.log (((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ))) / D := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have he (t : Fin D) : -Real.log (((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ)) =
      Real.log (D : ℝ) - Real.log ((D - (t : ℕ) : ℕ) : ℝ) := by
    rw [Real.log_div (by exact_mod_cast (Nat.sub_pos_of_lt t.isLt).ne') hD0.ne']
    ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, sum_log_sub]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h := log_factorial_upper D hD
  apply (le_div_iff₀ hD0).mpr
  have he : (1 - (1 + Real.log (D : ℝ)) / (D : ℝ)) * D =
      (D : ℝ) - (1 + Real.log (D : ℝ)) := by field_simp
  rw [he]
  linarith

lemma average_inverse_rank {D : ℕ} (hD : 0 < D) (a : ℝ) :
    (∑ t : Fin D, a / ((((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ)))) / D =
      a * (harmonic D : ℝ) := by
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have he (t : Fin D) : a / ((((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ))) =
      a * (1 / ((D - (t : ℕ) : ℕ) : ℝ)) * D := by field_simp
  simp_rw [he]
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_inv_sub, mul_div_cancel_right₀ _ hD0]

end ThorpCompatibility

end OAI
