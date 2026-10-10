import OAI.Analysis.FreeEntropy.SeriesWeights

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type} [Fintype α]

@[simp] theorem degreeNorm_nil (f : Series α) : degreeNorm f 0 = ‖f []‖ :=
  vdegreeNorm_zero_degree f
@[simp] theorem degreeNorm_unit_pos {n : ℕ} (hn : 0 < n) : degreeNorm (unit : Series α) n = 0 := by
  apply (degreeNorm_congr (g := 0) n ?_).trans (degreeNorm_zero n)
  intro w hw
  cases w with
  | nil => simp at hw; omega
  | cons a w => rfl
@[simp] theorem degreeNorm_neg (f : Series α) (n : ℕ) : degreeNorm (-f) n = degreeNorm f n := by
  change ‖-degreeVector f n‖ = _
  exact norm_neg _
 theorem degreeNorm_sub_unit_pos (f : Series α) {n : ℕ} (hn : 0 < n) :
    degreeNorm (f-unit) n = degreeNorm f n := by
  apply degreeNorm_congr
  intro w hw
  cases w with
  | nil => simp at hw; omega
  | cons a w => simp
 theorem seriesWeight_add_le (f g : Series α) {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    seriesWeight (f+g) r N ≤ seriesWeight f r N + seriesWeight g r N := by
  unfold seriesWeight truncEval
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro k hk
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (degreeNorm_add_le f g k) (pow_nonneg hr k)
@[simp] theorem seriesWeight_neg (f : Series α) (r : ℝ) (N : ℕ) :
    seriesWeight (-f) r N = seriesWeight f r N := by simp [seriesWeight, truncEval]
 theorem seriesWeight_agree {f g : Series α} {N : ℕ} (h : Agree N f g) (r : ℝ) :
    seriesWeight f r N = seriesWeight g r N := by
  unfold seriesWeight truncEval
  apply sum_congr rfl
  intro k hk
  congr 1
  exact degreeNorm_congr k (fun w hw => h w (by simp only [mem_range] at hk; omega))
 theorem seriesWeight_split {f : Series α} (hf : f [] = 1) (r : ℝ) (N : ℕ) :
    seriesWeight f r N = 1 + seriesWeight (f-unit) r N := by
  unfold seriesWeight truncEval
  rw [sum_range_succ', sum_range_succ']
  simp only [degreeNorm_nil, hf, norm_one, pow_zero, one_mul, Pi.sub_apply, unit_nil, sub_self, norm_zero, add_zero]
  simp only [degreeNorm_sub_unit_pos f (Nat.zero_lt_succ _)]
  ring
@[simp] theorem seriesWeight_unit (r : ℝ) (N : ℕ) : seriesWeight (unit : Series α) r N = 1 := by
  unfold seriesWeight truncEval
  rw [sum_range_succ']
  simp
 theorem inverse_tail_identity {α : Type} [Fintype α] {M : Series α} (hM : M [] = 1) :
    inverse M - unit = -(M-unit) - conv (M-unit) (inverse M-unit) := by
  rw [conv_sub_left, conv_sub_right, conv_sub_right, conv_inverse hM, conv_unit_left,
    conv_unit_right, conv_unit_left]
  abel
 theorem inverse_tail_weight {M : Series α} (hM : M [] = 1) {r a : ℝ} (hr : 0 ≤ r)
    (_ha : 0 ≤ a) (ha1 : a < 1) (N : ℕ) (h : seriesWeight (M-unit) r N ≤ a) :
    seriesWeight (inverse M-unit) r N ≤ a/(1-a) := by
  have hb := seriesWeight_nonneg (inverse M-unit) hr N
  have hie : seriesWeight (inverse M-unit) r N ≤
      seriesWeight (M-unit) r N + seriesWeight (M-unit) r N * seriesWeight (inverse M-unit) r N := by
    conv_lhs => rw [inverse_tail_identity hM]
    calc
      _ ≤ seriesWeight (-(M-unit)) r N + seriesWeight (-conv (M-unit) (inverse M-unit)) r N :=
        seriesWeight_add_le _ _ hr N
      _ ≤ _ := by simpa only [seriesWeight_neg] using
        add_le_add le_rfl (seriesWeight_conv_le (M-unit) (inverse M-unit) hr N)
  apply (le_div_iff₀ (by linarith : 0 < 1-a)).mpr
  have hh := mul_le_mul_of_nonneg_right h hb
  nlinarith
 theorem seriesWeight_coeff_le (f : Series α) {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    r^n * degreeNorm f n ≤ seriesWeight f r n := by
  exact single_le_sum (fun k _ => mul_nonneg (pow_nonneg hr k) (degreeNorm_nonneg f k))
    (mem_range.mpr (by omega))
 theorem degreeNorm_le_of_weight {f : Series α} {r : ℝ} (hr : 0 < r)
    (h : ∀ N, seriesWeight f r N ≤ 1) (n : ℕ) : degreeNorm f n ≤ (r⁻¹)^n := by
  have hn := (seriesWeight_coeff_le f hr.le n).trans (h n)
  rw [inv_pow, ← one_div]
  apply (le_div_iff₀ (pow_pos hr n)).mpr
  simpa only [mul_comm] using hn

 theorem seriesWeight_mono_radius (f : Series α) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (N : ℕ) :
    seriesWeight f r N ≤ seriesWeight f s N := by
  unfold seriesWeight truncEval
  apply sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr hrs k) (degreeNorm_nonneg f k)
 theorem geom_tail_le {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    (∑ k ∈ range (N+1), q^k) - 1 ≤ q/(1-q) := by
  apply (le_div_iff₀ (by linarith : 0 < 1-q)).mpr
  have he := geom_sum_mul_neg q (N+1)
  have hp := pow_nonneg hq (N+1)
  nlinarith
 theorem weight_le_geom {f : Series α} (hf : f [] = 0) {A r : ℝ}
    (hA : 0 ≤ A) (hr : 0 ≤ r) (hq : r*A < 1)
    (hb : ∀ n, 0 < n → degreeNorm f n ≤ A^n) (N : ℕ) :
    seriesWeight f r N ≤ (r*A)/(1-r*A) := by
  apply le_trans (b := (∑ k ∈ range (N+1), (r*A)^k) - 1) ?_
    (geom_tail_le (mul_nonneg hr hA) hq N)
  unfold seriesWeight truncEval
  rw [sum_range_succ', sum_range_succ']
  simp only [degreeNorm_nil, hf, norm_zero, pow_zero, mul_zero, add_zero]
  rw [add_sub_cancel_right]
  apply sum_le_sum
  intro k hk
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left (hb (k+1) (by omega)) (pow_nonneg hr _)
 theorem subst_weight_le (M f : Series α) {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    seriesWeight (subst M f) r N ≤ seriesWeight f (r*seriesWeight M r N) N := by
  apply (seriesWeight_subst_le M f hr N).trans_eq
  exact sum_congr rfl (fun k _ => mul_comm _ _)
 theorem moments_tail_weight {R : Series α} (hR : R [] = 0) {r a : ℝ}
    (hr : 0 ≤ r) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (h : ∀ N, seriesWeight R (2*r) N ≤ a) (N : ℕ) :
    seriesWeight (moments R-unit) r N ≤ a := by
  have hi (j : ℕ) (K : ℕ) : seriesWeight (momentIter R j-unit) r K ≤ a := by
    induction j with
    | zero => simpa [momentIter, seriesWeight, truncEval] using ha
    | succ j ih =>
      have hM : seriesWeight (momentIter R j) r K ≤ 2 := by
        rw [seriesWeight_split (momentIter_nil hR j)]
        linarith
      have ht : momentIter R (j+1)-unit = subst (momentIter R j) R := by
        rw [momentIter]; abel
      rw [ht]
      apply (subst_weight_le _ _ hr K).trans
      apply (seriesWeight_mono_radius R
        (mul_nonneg hr (seriesWeight_nonneg _ hr _))
        (by nlinarith : r*seriesWeight (momentIter R j) r K ≤ 2*r) K).trans
      exact h K
  apply le_of_eq_of_le (b := seriesWeight (momentIter R N-unit) r N) ?_ (hi N N)
  exact seriesWeight_agree (fun w hw => by simp only [Pi.sub_apply, moments_agree hR N w hw]) r

end FiniteEntropySeparation.FreeSeries

end

end OAI
