import OAI.NumberTheory.JointDickman.Amplification.ThreeFormLocalBound

namespace OAI

/-! # Three-form local means with independently tilted weights -/

namespace JointDickman

open Finset

open Classical in
theorem three_affine_residue_sum_mixed {p : ℕ} [Fact p.Prime]
    (j : ZMod p) (hj : j ≠ 0) (t u v : ℝ) :
    (∑ b : ZMod p, ∑ c : ZMod p,
      residueWeight t 0 b * residueWeight u 0 c * residueWeight v 0 (b + j * c)) =
      u * ((p : ℝ) - 1 + t * v) + ((p : ℝ) - 1) * ((p : ℝ) - 2 + t + v) := by
  rw [sum_comm]
  have hinner (c : ZMod p) : (∑ b : ZMod p,
      residueWeight t 0 b * residueWeight u 0 c * residueWeight v 0 (b + j * c)) =
      if c = 0 then u * ((p : ℝ) - 1 + t * v) else (p : ℝ) - 2 + t + v := by
    by_cases hc : c = 0
    · subst c
      simp only [mul_zero, add_zero, residueWeight, ite_true]
      calc
        _ = u * ∑ b : ZMod p, residueWeight (t * v) 0 b := by
          rw [mul_sum]
          apply sum_congr rfl
          intro b _
          by_cases hb : b = 0 <;> simp [residueWeight, hb]
          ring
        _ = _ := by rw [sum_residueWeight, ZMod.card]
    · have hroot : (0 : ZMod p) ≠ -(j * c) := by
        intro h
        exact mul_ne_zero hj hc (neg_eq_zero.mp h.symm)
      have heq (b : ZMod p) : residueWeight v 0 (b + j * c) = residueWeight v (-(j * c)) b := by
        simp [residueWeight, add_eq_zero_iff_eq_neg]
      simp only [hc, residueWeight, ite_false, mul_one]
      change (∑ b : ZMod p, residueWeight t 0 b * residueWeight v 0 (b + j * c)) = _
      simp_rw [heq]
      simpa only [ZMod.card] using sum_two_residueWeights t v (0 : ZMod p) (-(j * c)) hroot
  simp_rw [hinner]
  have heq (c : ZMod p) :
      (if c = 0 then u * ((p : ℝ) - 1 + t * v) else (p : ℝ) - 2 + t + v) =
      ((p : ℝ) - 2 + t + v) +
        (if c = 0 then u * ((p : ℝ) - 1 + t * v) - ((p : ℝ) - 2 + t + v) else 0) := by
    by_cases hc : c = 0 <;> simp [hc]
  simp_rw [heq]
  simp only [sum_add_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul, sum_ite_eq', mem_univ, ite_true]
  ring

noncomputable def mixedThreeFormMean {p : ℕ} [NeZero p]
    (j : ZMod p) (t u v : ℝ) : ℝ :=
  (∑ b : ZMod p, ∑ c : ZMod p,
    residueWeight t 0 b * residueWeight u 0 c * residueWeight v 0 (b + j * c)) / (p : ℝ) ^ 2

theorem mixedThreeFormMean_nonneg {p : ℕ} [NeZero p]
    (j : ZMod p) {t u v : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ mixedThreeFormMean j t u v :=
  div_nonneg (sum_nonneg (fun _b _ => sum_nonneg (fun _c _ =>
    mul_nonneg (mul_nonneg (residueWeight_nonneg _ _ ht) (residueWeight_nonneg _ _ hu))
      (residueWeight_nonneg _ _ hv)))) (sq_nonneg _)

theorem mixedThreeFormMean_le_one {p : ℕ} [NeZero p]
    (j : ZMod p) {t u v : ℝ} (_ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    mixedThreeFormMean j t u v ≤ 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  apply (div_le_one (sq_pos_of_pos hp0)).mpr
  calc
    _ ≤ ∑ _b : ZMod p, ∑ _c : ZMod p, (1 : ℝ) := by
      apply sum_le_sum
      intro b _
      apply sum_le_sum
      intro c _
      have htu : residueWeight t 0 b * residueWeight u 0 c ≤ 1 := by
        simpa only [mul_one] using mul_le_mul (residueWeight_le_one _ _ ht1)
          (residueWeight_le_one _ _ hu1) (residueWeight_nonneg _ _ hu) zero_le_one
      simpa only [mul_one] using mul_le_mul htu (residueWeight_le_one _ _ hv1)
        (residueWeight_nonneg _ _ hv) zero_le_one
    _ = _ := by simp [pow_two]

theorem mixedThreeFormMean_nondegenerate {p : ℕ} [Fact p.Prime]
    (j : ZMod p) (hj : j ≠ 0) {t u v : ℝ} (ht : t ≤ 1) (hu : u ≤ 1) (hv : v ≤ 1) :
    mixedThreeFormMean j t u v ≤
      (1 - (1 - t) / p) * (1 - (1 - u) / p) * (1 - (1 - v) / p) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hp0 : (0 : ℝ) < p := by linarith
  have heq : mixedThreeFormMean j t u v =
      (1 - (1 - t) / p) * (1 - (1 - u) / p) * (1 - (1 - v) / p) -
        (1 - t) * (1 - u) * (1 - v) * ((p : ℝ) - 1) / (p : ℝ) ^ 3 := by
    unfold mixedThreeFormMean
    rw [three_affine_residue_sum_mixed j hj]
    field_simp
    ring
  rw [heq]
  exact sub_le_self _ (by positivity)

theorem mixedThreeFormMean_bound {p : ℕ} [Fact p.Prime]
    (j : ZMod p) {t u v : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    mixedThreeFormMean j t u v ≤
      (1 - (1 - t) / p) * (1 - (1 - u) / p) * (1 - (1 - v) / p) *
        (if j = 0 then 1 + 24 / (p : ℝ) else 1) := by
  by_cases hj : j = 0
  · rw [ite_eq_left hj]
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hx : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    have hc : 1 ≤ (1 - 1 / (p : ℝ)) ^ 3 * (1 + 24 / (p : ℝ)) := by
      simpa only [one_mul, div_eq_mul_inv] using
        one_le_cube_singular_factor (by positivity : (0 : ℝ) ≤ 1 / p) hx (by norm_num : (0 : ℝ) ≤ 1) le_rfl
    have hmin : (1 - 1 / (p : ℝ)) ^ 3 ≤
        (1 - (1 - t) / p) * (1 - (1 - u) / p) * (1 - (1 - v) / p) := by
      have hbase : 0 ≤ 1 - 1 / (p : ℝ) := by linarith
      have ht' : 1 - 1 / (p : ℝ) ≤ 1 - (1 - t) / p := by
        have := div_nonneg ht hp0.le
        linarith [sub_div 1 t (p : ℝ)]
      have hu' : 1 - 1 / (p : ℝ) ≤ 1 - (1 - u) / p := by
        have := div_nonneg hu hp0.le
        linarith [sub_div 1 u (p : ℝ)]
      have hv' : 1 - 1 / (p : ℝ) ≤ 1 - (1 - v) / p := by
        have := div_nonneg hv hp0.le
        linarith [sub_div 1 v (p : ℝ)]
      calc
        _ = (1 - 1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) := by ring
        _ ≤ _ := mul_le_mul (mul_le_mul ht' hu' hbase (hbase.trans ht')) hv' hbase
          (mul_nonneg (hbase.trans ht') (hbase.trans hu'))
    exact (mixedThreeFormMean_le_one j ht ht1 hu hu1 hv hv1).trans
      (hc.trans (mul_le_mul_of_nonneg_right hmin (by positivity)))
  · rw [ite_eq_right hj, mul_one]
    exact mixedThreeFormMean_nondegenerate j hj ht1 hu1 hv1

end JointDickman

end OAI
