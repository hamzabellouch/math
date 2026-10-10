import OAI.NumberTheory.JointDickman.Amplification.AffineLocalFactors

namespace OAI

/-! # Local upper bounds for b, c, and b+jc

At primes not dividing j the exact three-form mean is bounded by the cube
of the single-form mean. Degenerate primes cost at most `1 + 24/p`.
-/

namespace JointDickman

open Finset

noncomputable def threeFormResidueMean {p : ℕ} [NeZero p] (j : ZMod p) (t : ℝ) : ℝ :=
  (∑ b : ZMod p, ∑ c : ZMod p,
    residueWeight t 0 b * residueWeight t 0 c * residueWeight t 0 (b + j * c)) / (p : ℝ) ^ 2

theorem residueWeight_nonneg {α : Type*} (a x : α) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ residueWeight t a x := by
  classical
  unfold residueWeight
  split_ifs <;> positivity

theorem residueWeight_le_one {α : Type*} (a x : α) {t : ℝ} (ht : t ≤ 1) :
    residueWeight t a x ≤ 1 := by
  classical
  unfold residueWeight
  split_ifs <;> linarith

theorem threeFormResidueMean_nonneg {p : ℕ} [NeZero p] (j : ZMod p) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ threeFormResidueMean j t := by
  unfold threeFormResidueMean
  exact div_nonneg (sum_nonneg (fun b _ => sum_nonneg (fun c _ =>
    mul_nonneg (mul_nonneg (residueWeight_nonneg _ _ ht) (residueWeight_nonneg _ _ ht))
      (residueWeight_nonneg _ _ ht)))) (sq_nonneg _)

theorem threeFormResidueMean_le_one {p : ℕ} [NeZero p] (j : ZMod p) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) : threeFormResidueMean j t ≤ 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  apply (div_le_one (sq_pos_of_pos hp0)).mpr
  calc
    _ ≤ ∑ _b : ZMod p, ∑ _c : ZMod p, (1 : ℝ) := by
      apply sum_le_sum
      intro b _
      apply sum_le_sum
      intro c _
      calc
        _ ≤ 1 * 1 := mul_le_mul
          (by
            have h := mul_le_mul (residueWeight_le_one (0 : ZMod p) b ht1)
              (residueWeight_le_one (0 : ZMod p) c ht1)
              (residueWeight_nonneg (0 : ZMod p) c ht) zero_le_one
            simpa only [mul_one] using h)
          (residueWeight_le_one _ _ ht1) (residueWeight_nonneg _ _ ht) zero_le_one
        _ = 1 := mul_one _
    _ = _ := by simp [pow_two]

theorem threeFormResidueMean_nondegenerate {p : ℕ} [Fact p.Prime]
    (j : ZMod p) (hj : j ≠ 0) {t : ℝ} (_ht : 0 ≤ t) (ht1 : t ≤ 1) :
    threeFormResidueMean j t ≤ (1 - (1 - t) / p) ^ 3 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hidentity : threeFormResidueMean j t = (1 - (1 - t) / p) ^ 3 -
      (1 - t) ^ 3 * ((p : ℝ) - 1) / (p : ℝ) ^ 3 := by
    unfold threeFormResidueMean
    rw [three_affine_residue_sum j hj]
    field_simp
    ring
  rw [hidentity]
  exact sub_le_self _ (by positivity)

theorem one_le_cube_singular_factor {x d : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    1 ≤ (1 - d * x) ^ 3 * (1 + 24 * x) := by
  have hdx : 0 ≤ d * x := mul_nonneg hd hx
  have hdxle : d * x ≤ x := mul_le_of_le_one_left hx hd1
  have hcube : (1 / 8 : ℝ) ≤ (1 - d * x) ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (show (1 / 2 : ℝ) ≤ 1 - d * x by linarith) 3
    norm_num at h
    exact h
  have hbernoulli : 1 - 3 * x ≤ (1 - d * x) ^ 3 := by
    have hprod := mul_nonneg (sq_nonneg (d * x)) (show 0 ≤ 3 - d * x by linarith)
    nlinarith
  have hextra := mul_le_mul_of_nonneg_left hcube (show 0 ≤ 24 * x by positivity)
  nlinarith

theorem threeFormResidueMean_bound {p : ℕ} [Fact p.Prime]
    (j : ZMod p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    threeFormResidueMean j t ≤ (1 - (1 - t) / p) ^ 3 *
      (if j = 0 then 1 + 24 / (p : ℝ) else 1) := by
  by_cases hj : j = 0
  · rw [ite_eq_left hj]
    refine (threeFormResidueMean_le_one j ht ht1).trans ?_
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
    have hx : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    simpa only [div_eq_mul_inv, one_mul] using one_le_cube_singular_factor
      (by positivity : (0 : ℝ) ≤ 1 / p) hx (by linarith : 0 ≤ 1 - t)
      (by linarith : 1 - t ≤ 1)
  · rw [ite_eq_right hj, mul_one]
    exact threeFormResidueMean_nondegenerate j hj ht ht1

end JointDickman

end OAI
