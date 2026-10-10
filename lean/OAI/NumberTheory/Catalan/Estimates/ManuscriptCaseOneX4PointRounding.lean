import OAI.NumberTheory.Catalan.Analysis.ManuscriptLogErrorBudgets
import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseOneX4Substitute
import OAI.NumberTheory.Catalan.Estimates.ManuscriptTermRounding

namespace OAI

section

namespace InternalCatalan

theorem manuscript_interval_abs_sub_le_width (a b q : ℚ) (x : ℝ)
    (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ))
    (hq : q ∈ Set.Icc a b) :
    |x - (q : ℝ)| ≤ ((b - a : ℚ) : ℝ) := by
  have hql : (a : ℝ) ≤ (q : ℝ) := (Rat.cast_le (K := ℝ)).mpr hq.1
  have hqu : (q : ℝ) ≤ (b : ℝ) := (Rat.cast_le (K := ℝ)).mpr hq.2
  rw [Rat.cast_sub]
  apply abs_le.mpr
  constructor <;> linarith [hx.1, hx.2]

theorem manuscript_interval_abs_sub_lt_of_width (a b q : ℚ) (x : ℝ) (ε : ℚ)
    (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ))
    (hq : q ∈ Set.Icc a b) (hw : b - a < ε) :
    |x - (q : ℝ)| < (ε : ℝ) := by
  exact (manuscript_interval_abs_sub_le_width a b q x hx hq).trans_lt
    ((Rat.cast_lt (K := ℝ)).mpr hw)

theorem manuscript_interval_abs_sub_le_rounded_width (a b q lo hi : ℚ) (x : ℝ)
    (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ))
    (hq : q ∈ Set.Icc a b) (hlo : lo ≤ a) (hhi : b ≤ hi) :
    |x - (q : ℝ)| ≤ ((hi - lo : ℚ) : ℝ) := by
  have hw : b - a ≤ hi - lo := by linarith
  exact (manuscript_interval_abs_sub_le_width a b q x hx hq).trans
    ((Rat.cast_le (K := ℝ)).mpr hw)

theorem manuscript_interval_abs_sub_lt_of_rounded_width (a b q lo hi ε : ℚ) (x : ℝ)
    (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ))
    (hq : q ∈ Set.Icc a b) (hlo : lo ≤ a) (hhi : b ≤ hi)
    (hw : hi - lo < ε) :
    |x - (q : ℝ)| < (ε : ℝ) := by
  exact (manuscript_interval_abs_sub_le_rounded_width a b q lo hi x hx hq hlo hhi).trans_lt
    ((Rat.cast_lt (K := ℝ)).mpr hw)

end InternalCatalan

end

section

noncomputable section
open scoped BigOperators

namespace InternalCatalan

def manuscriptComplexLogApprox (m k : ℤ) (y t : ℝ) : ℂ :=
  ⟨barrierScaledLogApprox m y / 2, barrierArgApprox k t⟩

theorem manuscript_real_log_error_le_101h0 (s : ℝ) (m : ℤ) (y : ℝ)
    (hnorm : s = (2 : ℝ) ^ m * y) (hy : y ∈ Set.Icc (1 : ℝ) 2)
    (hm : |(m : ℝ)| ≤ 100) :
    |Real.log s - barrierScaledLogApprox m y| ≤ 101 * barrierLogHError := by
  rw [hnorm]
  have he : 0 ≤ barrierLogHError := by unfold barrierLogHError; positivity
  exact (barrier_scaled_log_abs_error m hy).trans
    (mul_le_mul_of_nonneg_right (by linarith) he)

theorem manuscript_complex_log_norm_error_lt
    (z : ℂ) (m k : ℤ) (y r s : ℝ)
    (hm : |(m : ℝ)| ≤ 100)
    (hnorm : z.re ^ 2 + z.im ^ 2 = (2 : ℝ) ^ m * y)
    (hy : y ∈ Set.Icc (1 : ℝ) 2)
    (hrot : barrierOctantRotate k z = ⟨r, s⟩)
    (hr : 0 < r) (hs : |s| ≤ r / 2) (hk : |k| ≤ 4)
    (hpos : k = 4 → s ≤ 0) (hneg : k = -4 → 0 < s) :
    ‖Complex.log z - manuscriptComplexLogApprox m k y (s / r)‖ <
      (1 / 1000000000000000 : ℝ) := by
  have hreal := barrierComplexLog_re_error z m y hnorm hy
  have harg := barrierComplexArg_octant_error k z r s hrot hr hs hk hpos hneg
  have he : 0 ≤ barrierLogHError := by unfold barrierLogHError; positivity
  have hscale : (|(m : ℝ)| + 1) * barrierLogHError / 2 ≤
      101 * barrierLogHError / 2 := by
    have hh := mul_le_mul_of_nonneg_right (show |(m : ℝ)| + 1 ≤ 101 by linarith) he
    linarith
  calc
    _ ≤ |(Complex.log z - manuscriptComplexLogApprox m k y (s / r)).re| +
        |(Complex.log z - manuscriptComplexLogApprox m k y (s / r)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = |(Complex.log z).re - barrierScaledLogApprox m y / 2| +
        |Complex.arg z - barrierArgApprox k (s / r)| := by
      simp only [manuscriptComplexLogApprox, Complex.sub_re, Complex.sub_im,
        Complex.log_im]
    _ ≤ (|(m : ℝ)| + 1) * barrierLogHError / 2 + 9 * barrierAtanJ0 :=
      add_le_add hreal harg
    _ ≤ 101 * barrierLogHError / 2 + 9 * barrierAtanJ0 :=
      add_le_add hscale le_rfl
    _ < (1 / 1000000000000000 : ℝ) := by
      have hh := manuscript_log_error_constants.1
      linarith

theorem manuscript_finite_error_sum_le {ι : Type*} (S : Finset ι)
    (actual approx weight : ι → ℝ) (ε : ℝ)
    (herr : ∀ i ∈ S, |actual i - approx i| ≤ weight i * ε) :
    |(∑ i ∈ S, actual i) - ∑ i ∈ S, approx i| ≤ (∑ i ∈ S, weight i) * ε := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ S, |actual i - approx i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, weight i * ε := Finset.sum_le_sum herr
    _ = _ := (Finset.sum_mul S weight ε).symm

theorem manuscript_list_abs_sum_le_of_error {ι : Type*} (L : List ι)
    (error weight : ι → ℝ) (ε : ℝ)
    (herr : ∀ i ∈ L, |error i| ≤ weight i * ε) :
    |(L.map error).sum| ≤ (L.map weight).sum * ε := by
  revert herr
  induction L with
  | nil => intro herr; simp
  | cons a L ih =>
    intro herr
    have ha := herr a List.mem_cons_self
    have ht := ih (fun i hi => herr i (List.mem_cons_of_mem _ hi))
    simp only [List.map_cons, List.sum_cons]
    calc
      _ ≤ |error a| + |(L.map error).sum| := by
        simpa only [Real.norm_eq_abs] using norm_add_le (error a) (L.map error).sum
      _ ≤ weight a * ε + (L.map weight).sum * ε := add_le_add ha ht
      _ = _ := by ring

theorem manuscript_list_error_sum_le {ι : Type*} (L : List ι)
    (actual approx weight : ι → ℝ) (ε : ℝ)
    (herr : ∀ i ∈ L, |actual i - approx i| ≤ weight i * ε) :
    |(L.map actual).sum - (L.map approx).sum| ≤ (L.map weight).sum * ε := by
  have heq : (L.map actual).sum - (L.map approx).sum =
      (L.map (fun i => actual i - approx i)).sum := by
    clear herr
    induction L with
    | nil => simp
    | cons a L ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; ring
  rw [heq]
  exact manuscript_list_abs_sum_le_of_error L _ weight ε herr

theorem manuscript_weighted_complex_difference_le (c a b : ℂ) :
    |(c * a).re - (c * b).re| ≤ ‖c‖ * ‖a - b‖ := by
  calc
    _ = |(c * (a - b)).re| := by rw [mul_sub, Complex.sub_re]
    _ ≤ ‖c * (a - b)‖ := Complex.abs_re_le_norm _
    _ = _ := norm_mul _ _

theorem manuscript_finite_weighted_complex_error_le {ι : Type*} (S : Finset ι)
    (c actual approx : ι → ℂ) (ε : ℝ)
    (herr : ∀ i ∈ S, ‖actual i - approx i‖ ≤ ε) :
    |(∑ i ∈ S, (c i * actual i).re) - ∑ i ∈ S, (c i * approx i).re| ≤
      (∑ i ∈ S, ‖c i‖) * ε := by
  apply manuscript_finite_error_sum_le S _ _ (fun i => ‖c i‖) ε
  intro i hi
  exact (manuscript_weighted_complex_difference_le _ _ _).trans
    (mul_le_mul_of_nonneg_left (herr i hi) (norm_nonneg _))

theorem manuscript_list_weighted_complex_error_le {ι : Type*} (L : List ι)
    (c actual approx : ι → ℂ) (ε : ℝ)
    (herr : ∀ i ∈ L, ‖actual i - approx i‖ ≤ ε) :
    |(L.map (fun i => (c i * actual i).re)).sum -
      (L.map (fun i => (c i * approx i).re)).sum| ≤
        (L.map (fun i => ‖c i‖)).sum * ε := by
  apply manuscript_list_error_sum_le L _ _ (fun i => ‖c i‖) ε
  intro i hi
  exact (manuscript_weighted_complex_difference_le _ _ _).trans
    (mul_le_mul_of_nonneg_left (herr i hi) (norm_nonneg _))

theorem manuscript_sum_error_lt_norm_allowance_of_mass {ι : Type*}
    (S : Finset ι) (actual approx weight : ι → ℝ)
    (herr : ∀ i ∈ S, |actual i - approx i| ≤ weight i * (1 / 1000000000000000 : ℝ))
    (hmass : (∑ i ∈ S, weight i) ≤ (569 / 2 : ℝ)) :
    |(∑ i ∈ S, actual i) - ∑ i ∈ S, approx i| <
      (285 / 1000000000000000 : ℝ) := by
  apply (manuscript_finite_error_sum_le S actual approx weight _ herr).trans_lt
  calc
    _ ≤ (569 / 2 : ℝ) * (1 / 1000000000000000) :=
      mul_le_mul_of_nonneg_right hmass (by norm_num)
    _ < _ := by norm_num

theorem manuscript_sum_error_lt_X_allowance_of_mass {ι : Type*}
    (S : Finset ι) (actual approx weight : ι → ℝ)
    (herr : ∀ i ∈ S, |actual i - approx i| ≤ weight i * (1 / 1000000000000000 : ℝ))
    (hmass : (∑ i ∈ S, weight i) < 35) :
    |(∑ i ∈ S, actual i) - ∑ i ∈ S, approx i| <
      (35 / 1000000000000000 : ℝ) := by
  apply (manuscript_finite_error_sum_le S actual approx weight _ herr).trans_lt
  have hh := mul_lt_mul_of_pos_right hmass (by norm_num : (0 : ℝ) < 1 / 1000000000000000)
  simpa only [mul_one_div] using hh

theorem manuscript_sum_error_lt_Y_allowance_of_mass {ι : Type*}
    (S : Finset ι) (actual approx weight : ι → ℝ)
    (herr : ∀ i ∈ S, |actual i - approx i| ≤ weight i * (1 / 1000000000000000 : ℝ))
    (hmass : (∑ i ∈ S, weight i) < 14) :
    |(∑ i ∈ S, actual i) - ∑ i ∈ S, approx i| <
      (14 / 1000000000000000 : ℝ) := by
  apply (manuscript_finite_error_sum_le S actual approx weight _ herr).trans_lt
  have hh := mul_lt_mul_of_pos_right hmass (by norm_num : (0 : ℝ) < 1 / 1000000000000000)
  simpa only [mul_one_div] using hh

theorem manuscript_three_error_allowances_lt_coarse :
    (285 / 1000000000000000 : ℝ) < 1 / 100000000 ∧
    (35 / 1000000000000000 : ℝ) < 1 / 100000000 ∧
    (14 / 1000000000000000 : ℝ) < 1 / 100000000 := by norm_num

theorem manuscript_list_error_lt_norm_allowance_of_mass {ι : Type*}
    (L : List ι) (actual approx weight : ι → ℝ)
    (herr : ∀ i ∈ L, |actual i - approx i| ≤ weight i * (1 / 1000000000000000 : ℝ))
    (hmass : (L.map weight).sum ≤ (569 / 2 : ℝ)) :
    |(L.map actual).sum - (L.map approx).sum| < (285 / 1000000000000000 : ℝ) := by
  apply (manuscript_list_error_sum_le L actual approx weight _ herr).trans_lt
  calc
    _ ≤ (569 / 2 : ℝ) * (1 / 1000000000000000) :=
      mul_le_mul_of_nonneg_right hmass (by norm_num)
    _ < _ := by norm_num

theorem manuscript_list_error_lt_X_allowance_of_mass {ι : Type*}
    (L : List ι) (actual approx weight : ι → ℝ)
    (herr : ∀ i ∈ L, |actual i - approx i| ≤ weight i * (1 / 1000000000000000 : ℝ))
    (hmass : (L.map weight).sum < 35) :
    |(L.map actual).sum - (L.map approx).sum| < (35 / 1000000000000000 : ℝ) := by
  apply (manuscript_list_error_sum_le L actual approx weight _ herr).trans_lt
  have hh := mul_lt_mul_of_pos_right hmass (by norm_num : (0 : ℝ) < 1 / 1000000000000000)
  simpa only [mul_one_div] using hh

theorem manuscript_list_error_lt_Y_allowance_of_mass {ι : Type*}
    (L : List ι) (actual approx weight : ι → ℝ)
    (herr : ∀ i ∈ L, |actual i - approx i| ≤ weight i * (1 / 1000000000000000 : ℝ))
    (hmass : (L.map weight).sum < 14) :
    |(L.map actual).sum - (L.map approx).sum| < (14 / 1000000000000000 : ℝ) := by
  apply (manuscript_list_error_sum_le L actual approx weight _ herr).trans_lt
  have hh := mul_lt_mul_of_pos_right hmass (by norm_num : (0 : ℝ) < 1 / 1000000000000000)
  simpa only [mul_one_div] using hh

def manuscriptTermRoundStep : ℝ := 1 / (10 : ℝ) ^ 40

theorem manuscript_series_rounding_error_le (count : ℕ) (term rounded : ℕ → ℝ)
    (δ : ℝ) (herr : ∀ j ∈ Finset.range count, |term j - rounded j| ≤ δ) :
    |(∑ j ∈ Finset.range count, term j) - ∑ j ∈ Finset.range count, rounded j| ≤
      (count : ℝ) * δ := by
  have hh := manuscript_finite_error_sum_le (Finset.range count) term rounded
    (fun _ => (1 : ℝ)) δ (by simpa only [one_mul] using herr)
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] using hh

theorem manuscript_H_rounding_error_le (y : ℝ) (rounded : ℕ → ℝ)
    (δ : ℝ)
    (herr : ∀ j ∈ Finset.range 18,
      |((y - 1) / (y + 1)) ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) - rounded j| ≤ δ) :
    |barrierLogH y - 2 * ∑ j ∈ Finset.range 18, rounded j| ≤ 36 * δ := by
  have hh := manuscript_series_rounding_error_le 18
    (fun j => ((y - 1) / (y + 1)) ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ))
    rounded δ herr
  unfold barrierLogH
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hh2 := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2)
  norm_num only [Nat.cast_ofNat] at hh2
  linarith

theorem manuscript_J_rounding_error_le (t : ℝ) (rounded : ℕ → ℝ)
    (δ : ℝ)
    (herr : ∀ j ∈ Finset.range 24,
      |(-1 : ℝ) ^ j * t ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) - rounded j| ≤ δ) :
    |barrierAtanJ t - ∑ j ∈ Finset.range 24, rounded j| ≤ 24 * δ := by
  simpa only [barrierAtanJ, Nat.cast_ofNat] using
    manuscript_series_rounding_error_le 24
      (fun j => (-1 : ℝ) ^ j * t ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ))
      rounded δ herr

theorem manuscript_scaled_real_rounding_error_le_of_series_bounds
    (m : ℤ) (y Htwo Hy δ : ℝ) (hδ : 0 ≤ δ) (hm : |(m : ℝ)| ≤ 100)
    (hHtwo : |barrierLogH 2 - Htwo| ≤ 36 * δ)
    (hHy : |barrierLogH y - Hy| ≤ 36 * δ) :
    |barrierScaledLogApprox m y - ((m : ℝ) * Htwo + Hy)| ≤ 3636 * δ := by
  have hmH := mul_le_mul_of_nonneg_left hHtwo (abs_nonneg (m : ℝ))
  have hmδ := mul_le_mul_of_nonneg_right hm (show 0 ≤ 36 * δ by positivity)
  have ht := norm_add_le ((m : ℝ) * (barrierLogH 2 - Htwo)) (barrierLogH y - Hy)
  simp only [Real.norm_eq_abs, abs_mul] at ht
  have heq : barrierScaledLogApprox m y - ((m : ℝ) * Htwo + Hy) =
      (m : ℝ) * (barrierLogH 2 - Htwo) + (barrierLogH y - Hy) := by
    unfold barrierScaledLogApprox
    ring
  rw [heq]
  nlinarith

theorem manuscript_complex_rounding_error_le_of_series_bounds
    (m k : ℤ) (y t Htwo Hy Jhalf Jthird Jt δ : ℝ)
    (hδ : 0 ≤ δ) (hm : |(m : ℝ)| ≤ 100) (hk : |(k : ℝ)| ≤ 4)
    (hHtwo : |barrierLogH 2 - Htwo| ≤ 36 * δ)
    (hHy : |barrierLogH y - Hy| ≤ 36 * δ)
    (hJhalf : |barrierAtanJ (1 / 2) - Jhalf| ≤ 24 * δ)
    (hJthird : |barrierAtanJ (1 / 3) - Jthird| ≤ 24 * δ)
    (hJt : |barrierAtanJ t - Jt| ≤ 24 * δ) :
    ‖manuscriptComplexLogApprox m k y t -
      (⟨((m : ℝ) * Htwo + Hy) / 2, (k : ℝ) * (Jhalf + Jthird) + Jt⟩ : ℂ)‖ ≤
        2034 * δ := by
  have hreal : |barrierScaledLogApprox m y / 2 - ((m : ℝ) * Htwo + Hy) / 2| ≤
      1818 * δ := by
    have hh := manuscript_scaled_real_rounding_error_le_of_series_bounds m y Htwo Hy δ
      hδ hm hHtwo hHy
    rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have harg : |barrierArgApprox k t - ((k : ℝ) * (Jhalf + Jthird) + Jt)| ≤
      216 * δ := by
    have hsum : |(barrierAtanJ (1 / 2) - Jhalf) + (barrierAtanJ (1 / 3) - Jthird)| ≤
        48 * δ := by
      have ht := norm_add_le (barrierAtanJ (1 / 2) - Jhalf) (barrierAtanJ (1 / 3) - Jthird)
      simp only [Real.norm_eq_abs] at ht
      linarith
    have hkJ := mul_le_mul_of_nonneg_left hsum (abs_nonneg (k : ℝ))
    have hkδ := mul_le_mul_of_nonneg_right hk (show 0 ≤ 48 * δ by positivity)
    have ht := norm_add_le
      ((k : ℝ) * ((barrierAtanJ (1 / 2) - Jhalf) + (barrierAtanJ (1 / 3) - Jthird)))
      (barrierAtanJ t - Jt)
    simp only [Real.norm_eq_abs, abs_mul] at ht
    have heq : barrierArgApprox k t - ((k : ℝ) * (Jhalf + Jthird) + Jt) =
        (k : ℝ) * ((barrierAtanJ (1 / 2) - Jhalf) + (barrierAtanJ (1 / 3) - Jthird)) +
          (barrierAtanJ t - Jt) := by unfold barrierArgApprox; ring
    rw [heq]
    nlinarith
  have hnorm := Complex.norm_le_abs_re_add_abs_im
    (manuscriptComplexLogApprox m k y t -
      (⟨((m : ℝ) * Htwo + Hy) / 2, (k : ℝ) * (Jhalf + Jthird) + Jt⟩ : ℂ))
  simp only [manuscriptComplexLogApprox, Complex.sub_re, Complex.sub_im] at hnorm ⊢
  linarith

theorem manuscript_rounding_sum_lt_of_mass {ι : Type*}
    (S : Finset ι) (actual approx weight : ι → ℝ)
    (herr : ∀ i ∈ S, |actual i - approx i| ≤ weight i * (3636 * manuscriptTermRoundStep))
    (hmass : (∑ i ∈ S, weight i) ≤ (569 / 2 : ℝ)) :
    |(∑ i ∈ S, actual i) - ∑ i ∈ S, approx i| < (1 / (10 : ℝ) ^ 32) := by
  apply (manuscript_finite_error_sum_le S actual approx weight _ herr).trans_lt
  calc
    _ ≤ (569 / 2 : ℝ) * (3636 * manuscriptTermRoundStep) :=
      mul_le_mul_of_nonneg_right hmass (by unfold manuscriptTermRoundStep; positivity)
    _ < _ := by norm_num [manuscriptTermRoundStep]

theorem manuscript_list_rounding_sum_lt_of_mass {ι : Type*}
    (L : List ι) (actual approx weight : ι → ℝ)
    (herr : ∀ i ∈ L, |actual i - approx i| ≤ weight i * (3636 * manuscriptTermRoundStep))
    (hmass : (L.map weight).sum ≤ (569 / 2 : ℝ)) :
    |(L.map actual).sum - (L.map approx).sum| < (1 / (10 : ℝ) ^ 32) := by
  apply (manuscript_list_error_sum_le L actual approx weight _ herr).trans_lt
  calc
    _ ≤ (569 / 2 : ℝ) * (3636 * manuscriptTermRoundStep) :=
      mul_le_mul_of_nonneg_right hmass (by unfold manuscriptTermRoundStep; positivity)
    _ < _ := by norm_num [manuscriptTermRoundStep]

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan
open scoped BigOperators

def manuscriptRoundDownRat (q : ℚ) : ℚ :=
  ((⌊q / manuscriptTermRoundStepRat⌋ : ℤ) : ℚ) * manuscriptTermRoundStepRat

def manuscriptRoundUpRat (q : ℚ) : ℚ :=
  ((⌊q / manuscriptTermRoundStepRat⌋ + 1 : ℤ) : ℚ) * manuscriptTermRoundStepRat

theorem manuscript_round_rat_enclosure (q : ℚ) :
    manuscriptRoundDownRat q ≤ q ∧ q ≤ manuscriptRoundUpRat q ∧
      manuscriptRoundUpRat q - manuscriptRoundDownRat q = manuscriptTermRoundStepRat ∧
      |q - manuscriptRoundDownRat q| ≤ manuscriptTermRoundStepRat ∧
      |q - manuscriptRoundUpRat q| ≤ manuscriptTermRoundStepRat := by
  let k : ℤ := ⌊q / manuscriptTermRoundStepRat⌋
  have hδ : 0 < manuscriptTermRoundStepRat := by
    norm_num [manuscriptTermRoundStepRat]
  have hflo : (k : ℚ) ≤ q / manuscriptTermRoundStepRat :=
    Int.floor_le (q / manuscriptTermRoundStepRat)
  have hfhi : q / manuscriptTermRoundStepRat < ((k + 1 : ℤ) : ℚ) := by
    simpa only [Int.cast_add, Int.cast_one] using
      Int.lt_floor_add_one (q / manuscriptTermRoundStepRat)
  have hlo : (k : ℚ) * manuscriptTermRoundStepRat ≤ q :=
    (le_div_iff₀ hδ).mp hflo
  have hhi : q < ((k + 1 : ℤ) : ℚ) * manuscriptTermRoundStepRat :=
    (div_lt_iff₀ hδ).mp hfhi
  have hgap : ((k + 1 : ℤ) : ℚ) * manuscriptTermRoundStepRat -
      (k : ℚ) * manuscriptTermRoundStepRat = manuscriptTermRoundStepRat := by
    rw [Int.cast_add, Int.cast_one]
    ring
  change (k : ℚ) * manuscriptTermRoundStepRat ≤ q ∧
    q ≤ ((k + 1 : ℤ) : ℚ) * manuscriptTermRoundStepRat ∧
    ((k + 1 : ℤ) : ℚ) * manuscriptTermRoundStepRat -
      (k : ℚ) * manuscriptTermRoundStepRat = manuscriptTermRoundStepRat ∧
    |q - (k : ℚ) * manuscriptTermRoundStepRat| ≤ manuscriptTermRoundStepRat ∧
    |q - ((k + 1 : ℤ) : ℚ) * manuscriptTermRoundStepRat| ≤ manuscriptTermRoundStepRat
  refine ⟨hlo, hhi.le, hgap, ?_, ?_⟩
  · rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
    linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr hhi.le)]
    linarith

private theorem manuscript_round_step_cast :
    (manuscriptTermRoundStepRat : ℝ) = manuscriptTermRoundStep := by
  norm_num [manuscriptTermRoundStepRat, manuscriptTermRoundStep]

theorem manuscript_round_down_cast_error_le (q : ℚ) :
    |(q : ℝ) - (manuscriptRoundDownRat q : ℝ)| ≤ manuscriptTermRoundStep := by
  have h := (Rat.cast_le (K := ℝ)).mpr (manuscript_round_rat_enclosure q).2.2.2.1
  simpa only [Rat.cast_abs, Rat.cast_sub, manuscript_round_step_cast] using h

theorem manuscript_round_up_cast_error_le (q : ℚ) :
    |(q : ℝ) - (manuscriptRoundUpRat q : ℝ)| ≤ manuscriptTermRoundStep := by
  have h := (Rat.cast_le (K := ℝ)).mpr (manuscript_round_rat_enclosure q).2.2.2.2
  simpa only [Rat.cast_abs, Rat.cast_sub, manuscript_round_step_cast] using h

def manuscriptHInnerRat (y : ℚ) (j : ℕ) : ℚ :=
  ((y - 1) / (y + 1)) ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℚ)

def manuscriptJTermRat (t : ℚ) (j : ℕ) : ℚ :=
  (-1 : ℚ) ^ j * t ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℚ)

def manuscriptRoundedHRat (y : ℚ) : ℚ :=
  2 * ∑ j ∈ Finset.range 18, manuscriptRoundDownRat (manuscriptHInnerRat y j)

def manuscriptRoundedJRat (t : ℚ) : ℚ :=
  ∑ j ∈ Finset.range 24, manuscriptRoundDownRat (manuscriptJTermRat t j)

def manuscriptRoundedScaledLogRat (m : ℤ) (y : ℚ) : ℚ :=
  (m : ℚ) * manuscriptRoundedHRat 2 + manuscriptRoundedHRat y

def manuscriptRoundedArgRat (k : ℤ) (t : ℚ) : ℚ :=
  (k : ℚ) * (manuscriptRoundedJRat (1 / 2) + manuscriptRoundedJRat (1 / 3)) +
    manuscriptRoundedJRat t

def manuscriptRoundedComplexLog (m k : ℤ) (y t : ℚ) : ℂ :=
  ⟨((manuscriptRoundedScaledLogRat m y / 2 : ℚ) : ℝ),
    (manuscriptRoundedArgRat k t : ℝ)⟩

private theorem manuscript_round_sum_cast (count : ℕ) (f : ℕ → ℚ) :
    ((∑ j ∈ Finset.range count, f j : ℚ) : ℝ) =
      ∑ j ∈ Finset.range count, (f j : ℝ) :=
  map_sum (Rat.castHom ℝ) f (Finset.range count)

theorem manuscript_rounded_H_error_le (y : ℚ) :
    |barrierLogH (y : ℝ) - (manuscriptRoundedHRat y : ℝ)| ≤
      36 * manuscriptTermRoundStep := by
  have h := manuscript_H_rounding_error_le (y : ℝ)
    (fun j => (manuscriptRoundDownRat (manuscriptHInnerRat y j) : ℝ))
    manuscriptTermRoundStep (by
      intro j hj
      have hh := manuscript_round_down_cast_error_le (manuscriptHInnerRat y j)
      simpa only [manuscriptHInnerRat, Rat.cast_div, Rat.cast_pow, Rat.cast_sub,
        Rat.cast_one, Rat.cast_add, Rat.cast_natCast] using hh)
  simpa only [manuscriptRoundedHRat, Rat.cast_mul, Rat.cast_ofNat,
    manuscript_round_sum_cast] using h

theorem manuscript_rounded_J_error_le (t : ℚ) :
    |barrierAtanJ (t : ℝ) - (manuscriptRoundedJRat t : ℝ)| ≤
      24 * manuscriptTermRoundStep := by
  have h := manuscript_J_rounding_error_le (t : ℝ)
    (fun j => (manuscriptRoundDownRat (manuscriptJTermRat t j) : ℝ))
    manuscriptTermRoundStep (by
      intro j hj
      have hh := manuscript_round_down_cast_error_le (manuscriptJTermRat t j)
      simpa only [manuscriptJTermRat, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
        Rat.cast_neg, Rat.cast_one, Rat.cast_natCast] using hh)
  simpa only [manuscriptRoundedJRat, manuscript_round_sum_cast] using h

theorem manuscript_rounded_scaled_log_error_le (m : ℤ) (y : ℚ)
    (hm : |(m : ℝ)| ≤ 100) :
    |barrierScaledLogApprox m (y : ℝ) - (manuscriptRoundedScaledLogRat m y : ℝ)| ≤
      3636 * manuscriptTermRoundStep := by
  have hHtwo : |barrierLogH 2 - (manuscriptRoundedHRat 2 : ℝ)| ≤
      36 * manuscriptTermRoundStep := by
    simpa only [Rat.cast_ofNat] using manuscript_rounded_H_error_le (2 : ℚ)
  have h := manuscript_scaled_real_rounding_error_le_of_series_bounds m (y : ℝ)
    (manuscriptRoundedHRat 2 : ℝ) (manuscriptRoundedHRat y : ℝ)
    manuscriptTermRoundStep (by norm_num [manuscriptTermRoundStep]) hm hHtwo
    (manuscript_rounded_H_error_le y)
  simpa only [manuscriptRoundedScaledLogRat, Rat.cast_add, Rat.cast_mul,
    Rat.cast_intCast] using h

theorem manuscript_rounded_complex_log_error_le (m k : ℤ) (y t : ℚ)
    (hm : |(m : ℝ)| ≤ 100) (hk : |(k : ℝ)| ≤ 4) :
    ‖manuscriptComplexLogApprox m k (y : ℝ) (t : ℝ) -
      manuscriptRoundedComplexLog m k y t‖ ≤ 2034 * manuscriptTermRoundStep := by
  have hHtwo : |barrierLogH 2 - (manuscriptRoundedHRat 2 : ℝ)| ≤
      36 * manuscriptTermRoundStep := by
    simpa only [Rat.cast_ofNat] using manuscript_rounded_H_error_le (2 : ℚ)
  have hJhalf : |barrierAtanJ (1 / 2) - (manuscriptRoundedJRat (1 / 2) : ℝ)| ≤
      24 * manuscriptTermRoundStep := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      manuscript_rounded_J_error_le (1 / 2 : ℚ)
  have hJthird : |barrierAtanJ (1 / 3) - (manuscriptRoundedJRat (1 / 3) : ℝ)| ≤
      24 * manuscriptTermRoundStep := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      manuscript_rounded_J_error_le (1 / 3 : ℚ)
  have h := manuscript_complex_rounding_error_le_of_series_bounds m k (y : ℝ) (t : ℝ)
    (manuscriptRoundedHRat 2 : ℝ) (manuscriptRoundedHRat y : ℝ)
    (manuscriptRoundedJRat (1 / 2) : ℝ) (manuscriptRoundedJRat (1 / 3) : ℝ)
    (manuscriptRoundedJRat t : ℝ) manuscriptTermRoundStep
    (by norm_num [manuscriptTermRoundStep]) hm hk hHtwo
    (manuscript_rounded_H_error_le y) hJhalf hJthird (manuscript_rounded_J_error_le t)
  simpa only [manuscriptRoundedComplexLog, manuscriptRoundedScaledLogRat,
    manuscriptRoundedArgRat, Rat.cast_div, Rat.cast_ofNat, Rat.cast_add,
    Rat.cast_mul, Rat.cast_intCast] using h

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan

def manuscriptRoundedWeightedComplexLogRat (c d : ℚ) (m k : ℤ) (y t : ℚ) : ℚ :=
  c * (manuscriptRoundedScaledLogRat m y / 2) - d * manuscriptRoundedArgRat k t

def manuscriptRoundedXFieldRat (c v : ℚ) (m0 m1 m2 : ℤ) (y0 y1 y2 : ℚ) : ℚ :=
  (19 / 48 : ℚ) * manuscriptRoundedScaledLogRat m0 y0 +
    (1 / 12 : ℚ) * manuscriptRoundedScaledLogRat m1 y1 -
    c * manuscriptRoundedScaledLogRat m2 y2 + v

def manuscriptRoundedYFieldRat (v : ℚ) (m0 m1 : ℤ) (y0 y1 : ℚ) : ℚ :=
  (7 / 48 : ℚ) * manuscriptRoundedScaledLogRat m0 y0 +
    (1 / 12 : ℚ) * manuscriptRoundedScaledLogRat m1 y1 + v

theorem manuscript_rat_add_rounding_error (a ar b br : ℚ) {ε η : ℝ}
    (ha : |(a : ℝ) - (ar : ℝ)| ≤ ε)
    (hb : |(b : ℝ) - (br : ℝ)| ≤ η) :
    |((a + b : ℚ) : ℝ) - ((ar + br : ℚ) : ℝ)| ≤ ε + η := by
  simp only [Rat.cast_add]
  calc
    _ = |((a : ℝ) - (ar : ℝ)) + ((b : ℝ) - (br : ℝ))| := by congr 1; ring
    _ ≤ |(a : ℝ) - (ar : ℝ)| + |(b : ℝ) - (br : ℝ)| := abs_add_le _ _
    _ ≤ ε + η := add_le_add ha hb

private theorem manuscript_rat_mul_rounding_error (c a ar : ℚ) {ε : ℝ}
    (ha : |(a : ℝ) - (ar : ℝ)| ≤ ε) :
    |((c * a : ℚ) : ℝ) - ((c * ar : ℚ) : ℝ)| ≤ |(c : ℝ)| * ε := by
  simp only [Rat.cast_mul]
  calc
    _ = |(c : ℝ)| * |(a : ℝ) - (ar : ℝ)| := by rw [← mul_sub, abs_mul]
    _ ≤ |(c : ℝ)| * ε := mul_le_mul_of_nonneg_left ha (abs_nonneg _)

private theorem manuscript_rounded_scaled_rat_error_le (m : ℤ) (y : ℚ)
    (hm : |(m : ℝ)| ≤ 100) :
    |(barrierScaledLogRat m y : ℝ) - (manuscriptRoundedScaledLogRat m y : ℝ)| ≤
      3636 * manuscriptTermRoundStep := by
  rw [barrierScaledLogRat_cast]
  exact manuscript_rounded_scaled_log_error_le m y hm

theorem manuscript_rounded_weighted_complex_log_error_le
    (c d : ℚ) (m k : ℤ) (y t : ℚ)
    (hm : |(m : ℝ)| ≤ 100) (hk : |(k : ℝ)| ≤ 4) :
    |(barrierWeightedComplexLogRat c d m k y t : ℝ) -
      (manuscriptRoundedWeightedComplexLogRat c d m k y t : ℝ)| ≤
      (|(c : ℝ)| + |(d : ℝ)|) * (3636 * manuscriptTermRoundStep) := by
  have horiginal : (barrierWeightedComplexLogRat c d m k y t : ℝ) =
      (barrierComplex c d * manuscriptComplexLogApprox m k (y : ℝ) (t : ℝ)).re := by
    rw [barrierWeightedComplexLogRat_cast, Complex.mul_re]
    rfl
  have hrounded : (manuscriptRoundedWeightedComplexLogRat c d m k y t : ℝ) =
      (barrierComplex c d * manuscriptRoundedComplexLog m k y t).re := by
    simp only [manuscriptRoundedWeightedComplexLogRat, manuscriptRoundedComplexLog,
      Complex.mul_re, barrierComplex, Rat.cast_sub, Rat.cast_mul]
  have hcoeff : ‖barrierComplex c d‖ ≤ |(c : ℝ)| + |(d : ℝ)| := by
    simpa only [barrierComplex] using
      Complex.norm_le_abs_re_add_abs_im (barrierComplex c d)
  have hδ : 0 ≤ manuscriptTermRoundStep := by norm_num [manuscriptTermRoundStep]
  rw [horiginal, hrounded]
  calc
    _ ≤ ‖barrierComplex c d‖ *
        ‖manuscriptComplexLogApprox m k (y : ℝ) (t : ℝ) -
          manuscriptRoundedComplexLog m k y t‖ :=
      manuscript_weighted_complex_difference_le _ _ _
    _ ≤ ‖barrierComplex c d‖ * (2034 * manuscriptTermRoundStep) :=
      mul_le_mul_of_nonneg_left
        (manuscript_rounded_complex_log_error_le m k y t hm hk) (norm_nonneg _)
    _ ≤ (|(c : ℝ)| + |(d : ℝ)|) * (2034 * manuscriptTermRoundStep) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ ≤ (|(c : ℝ)| + |(d : ℝ)|) * (3636 * manuscriptTermRoundStep) :=
      mul_le_mul_of_nonneg_left (by nlinarith)
        (add_nonneg (abs_nonneg _) (abs_nonneg _))

theorem manuscript_rounded_x_field_error_le (c v : ℚ)
    (m0 m1 m2 : ℤ) (y0 y1 y2 : ℚ)
    (hm0 : |(m0 : ℝ)| ≤ 100) (hm1 : |(m1 : ℝ)| ≤ 100)
    (hm2 : |(m2 : ℝ)| ≤ 100) :
    |(((19 / 48 : ℚ) * barrierScaledLogRat m0 y0 +
      (1 / 12 : ℚ) * barrierScaledLogRat m1 y1 -
      c * barrierScaledLogRat m2 y2 + v : ℚ) : ℝ) -
      (manuscriptRoundedXFieldRat c v m0 m1 m2 y0 y1 y2 : ℝ)| ≤
      ((19 / 48 : ℝ) + 1 / 12 + |(c : ℝ)|) *
        (3636 * manuscriptTermRoundStep) := by
  have h0 := manuscript_rat_mul_rounding_error (19 / 48)
    (barrierScaledLogRat m0 y0) (manuscriptRoundedScaledLogRat m0 y0)
    (manuscript_rounded_scaled_rat_error_le m0 y0 hm0)
  have h1 := manuscript_rat_mul_rounding_error (1 / 12)
    (barrierScaledLogRat m1 y1) (manuscriptRoundedScaledLogRat m1 y1)
    (manuscript_rounded_scaled_rat_error_le m1 y1 hm1)
  have h2 := manuscript_rat_mul_rounding_error (-c)
    (barrierScaledLogRat m2 y2) (manuscriptRoundedScaledLogRat m2 y2)
    (manuscript_rounded_scaled_rat_error_le m2 y2 hm2)
  have h01 := manuscript_rat_add_rounding_error _ _ _ _ h0 h1
  have h012 := manuscript_rat_add_rounding_error _ _ _ _ h01 h2
  have hv : |(v : ℝ) - (v : ℝ)| ≤ (0 : ℝ) := by simp
  have h := manuscript_rat_add_rounding_error _ _ _ _ h012 hv
  have h19 : |((19 / 48 : ℚ) : ℝ)| = (19 / 48 : ℝ) := by norm_num
  have h12 : |((1 / 12 : ℚ) : ℝ)| = (1 / 12 : ℝ) := by norm_num
  simpa only [manuscriptRoundedXFieldRat, Rat.cast_neg, abs_neg, h19, h12,
    add_zero, add_mul, sub_eq_add_neg, neg_mul] using h

theorem manuscript_rounded_y_field_error_le (v : ℚ)
    (m0 m1 : ℤ) (y0 y1 : ℚ)
    (hm0 : |(m0 : ℝ)| ≤ 100) (hm1 : |(m1 : ℝ)| ≤ 100) :
    |(((7 / 48 : ℚ) * barrierScaledLogRat m0 y0 +
      (1 / 12 : ℚ) * barrierScaledLogRat m1 y1 + v : ℚ) : ℝ) -
      (manuscriptRoundedYFieldRat v m0 m1 y0 y1 : ℝ)| ≤
      ((7 / 48 : ℝ) + 1 / 12) * (3636 * manuscriptTermRoundStep) := by
  have h0 := manuscript_rat_mul_rounding_error (7 / 48)
    (barrierScaledLogRat m0 y0) (manuscriptRoundedScaledLogRat m0 y0)
    (manuscript_rounded_scaled_rat_error_le m0 y0 hm0)
  have h1 := manuscript_rat_mul_rounding_error (1 / 12)
    (barrierScaledLogRat m1 y1) (manuscriptRoundedScaledLogRat m1 y1)
    (manuscript_rounded_scaled_rat_error_le m1 y1 hm1)
  have h01 := manuscript_rat_add_rounding_error _ _ _ _ h0 h1
  have hv : |(v : ℝ) - (v : ℝ)| ≤ (0 : ℝ) := by simp
  have h := manuscript_rat_add_rounding_error _ _ _ _ h01 hv
  have h7 : |((7 / 48 : ℚ) : ℝ)| = (7 / 48 : ℝ) := by norm_num
  have h12 : |((1 / 12 : ℚ) : ℝ)| = (1 / 12 : ℝ) := by norm_num
  simpa only [manuscriptRoundedYFieldRat, h7, h12, add_zero, add_mul] using h

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def manuscriptCase1X0SubstituteRat : ℚ :=
  barrierCase1XApproxRat Case1PointData.X0 (-1) (0) (0) (1983459957 / 1000000000) (3983459957 / 2000000000) (7934113401022441849 / 4000000000000000000)

theorem manuscript_case1X0_substitute_interval :
    manuscriptCase1X0SubstituteRat ∈ Set.Icc manuscriptCase1X0Interval.1 manuscriptCase1X0Interval.2 := by
  have hf := manuscript_x_substitute_interval (41 / 48) (barrierCase1XRat Case1PointData.X0) (-1) (0) (0) (1983459957 / 1000000000) (3983459957 / 2000000000) (7934113401022441849 / 4000000000000000000) (by norm_num) (by norm_num) (by norm_num)
  change (barrierCase1XApproxRat Case1PointData.X0 (-1) (0) (0) (1983459957 / 1000000000) (3983459957 / 2000000000) (7934113401022441849 / 4000000000000000000)) ∈ Set.Icc manuscriptCase1X0Interval.1 manuscriptCase1X0Interval.2 at hf
  exact hf

theorem manuscript_case1X0_substitute_cutoff :
    manuscriptCase1X0SubstituteRat < ((-66221 / 50000) : ℚ) := by
  have hp : Case1PointData.X0PrintedUpper < ((-66221 / 50000) : ℚ) := by norm_num [Case1PointData.X0PrintedUpper]
  exact manuscript_case1X0_substitute_interval.2.trans_lt (manuscript_case1X0_endpoint_lt_printed.trans hp)

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def manuscriptCase1X1SubstituteRat : ℚ :=
  barrierCase1XApproxRat Case1PointData.X1 (-3) (0) (0) (2259572153 / 1250000000) (12259572153 / 10000000000) (105105666314613055409 / 100000000000000000000)

theorem manuscript_case1X1_substitute_interval :
    manuscriptCase1X1SubstituteRat ∈ Set.Icc manuscriptCase1X1Interval.1 manuscriptCase1X1Interval.2 := by
  have hf := manuscript_x_substitute_interval (41 / 48) (barrierCase1XRat Case1PointData.X1) (-3) (0) (0) (2259572153 / 1250000000) (12259572153 / 10000000000) (105105666314613055409 / 100000000000000000000) (by norm_num) (by norm_num) (by norm_num)
  change (barrierCase1XApproxRat Case1PointData.X1 (-3) (0) (0) (2259572153 / 1250000000) (12259572153 / 10000000000) (105105666314613055409 / 100000000000000000000)) ∈ Set.Icc manuscriptCase1X1Interval.1 manuscriptCase1X1Interval.2 at hf
  exact hf

theorem manuscript_case1X1_substitute_cutoff :
    manuscriptCase1X1SubstituteRat < ((-66221 / 50000) : ℚ) := by
  have hp : Case1PointData.X1PrintedUpper < ((-66221 / 50000) : ℚ) := by norm_num [Case1PointData.X1PrintedUpper]
  exact manuscript_case1X1_substitute_interval.2.trans_lt (manuscript_case1X1_endpoint_lt_printed.trans hp)

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def manuscriptCase1X2SubstituteRat : ℚ :=
  barrierCase1XApproxRat Case1PointData.X2 (-2) (-1) (0) (1271904013 / 1250000000) (3728095987 / 2500000000) (26617739818285504169 / 25000000000000000000)

theorem manuscript_case1X2_substitute_interval :
    manuscriptCase1X2SubstituteRat ∈ Set.Icc manuscriptCase1X2Interval.1 manuscriptCase1X2Interval.2 := by
  have hf := manuscript_x_substitute_interval (41 / 48) (barrierCase1XRat Case1PointData.X2) (-2) (-1) (0) (1271904013 / 1250000000) (3728095987 / 2500000000) (26617739818285504169 / 25000000000000000000) (by norm_num) (by norm_num) (by norm_num)
  change (barrierCase1XApproxRat Case1PointData.X2 (-2) (-1) (0) (1271904013 / 1250000000) (3728095987 / 2500000000) (26617739818285504169 / 25000000000000000000)) ∈ Set.Icc manuscriptCase1X2Interval.1 manuscriptCase1X2Interval.2 at hf
  exact hf

theorem manuscript_case1X2_substitute_cutoff :
    manuscriptCase1X2SubstituteRat < ((-66221 / 50000) : ℚ) := by
  have hp : Case1PointData.X2PrintedUpper < ((-66221 / 50000) : ℚ) := by norm_num [Case1PointData.X2PrintedUpper]
  exact manuscript_case1X2_substitute_interval.2.trans_lt (manuscript_case1X2_endpoint_lt_printed.trans hp)

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def manuscriptCase1X3SubstituteRat : ℚ :=
  barrierCase1XApproxRat Case1PointData.X3 (-2) (-1) (0) (4437270259 / 2500000000) (5562729741 / 5000000000) (119689367351405927081 / 100000000000000000000)

theorem manuscript_case1X3_substitute_interval :
    manuscriptCase1X3SubstituteRat ∈ Set.Icc manuscriptCase1X3Interval.1 manuscriptCase1X3Interval.2 := by
  have hf := manuscript_x_substitute_interval (41 / 48) (barrierCase1XRat Case1PointData.X3) (-2) (-1) (0) (4437270259 / 2500000000) (5562729741 / 5000000000) (119689367351405927081 / 100000000000000000000) (by norm_num) (by norm_num) (by norm_num)
  change (barrierCase1XApproxRat Case1PointData.X3 (-2) (-1) (0) (4437270259 / 2500000000) (5562729741 / 5000000000) (119689367351405927081 / 100000000000000000000)) ∈ Set.Icc manuscriptCase1X3Interval.1 manuscriptCase1X3Interval.2 at hf
  exact hf

theorem manuscript_case1X3_substitute_cutoff :
    manuscriptCase1X3SubstituteRat < ((-66221 / 50000) : ℚ) := by
  have hp : Case1PointData.X3PrintedUpper < ((-66221 / 50000) : ℚ) := by norm_num [Case1PointData.X3PrintedUpper]
  exact manuscript_case1X3_substitute_interval.2.trans_lt (manuscript_case1X3_endpoint_lt_printed.trans hp)

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def manuscriptCase1X0RoundedSubstituteRat : ℚ :=
  manuscriptRoundedXFieldRat (41 / 48) (barrierCase1XRat Case1PointData.X0) (-1) (0) (0) (1983459957 / 1000000000) (3983459957 / 2000000000) (7934113401022441849 / 4000000000000000000)

theorem manuscript_case1X0_additional_rounding_error :
    |(manuscriptCase1X0SubstituteRat : ℝ) - (manuscriptCase1X0RoundedSubstituteRat : ℝ)| < (1 / 10 ^ 32 : ℝ) := by
  let a0 : ℚ := barrierCase1XApproxRat Case1PointData.X0 (-1) (0) (0) (1983459957 / 1000000000) (3983459957 / 2000000000) (7934113401022441849 / 4000000000000000000)
  let r0 : ℚ := manuscriptRoundedXFieldRat (41 / 48) (barrierCase1XRat Case1PointData.X0) (-1) (0) (0) (1983459957 / 1000000000) (3983459957 / 2000000000) (7934113401022441849 / 4000000000000000000)
  let e0 : ℝ := ((19 / 48 : ℝ) + 1 / 12 + |(((41 / 48) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  have h0 : |(a0 : ℝ) - (r0 : ℝ)| ≤ e0 := by
    exact manuscript_rounded_x_field_error_le (41 / 48) (barrierCase1XRat Case1PointData.X0) (-1) (0) (0) (1983459957 / 1000000000) (3983459957 / 2000000000) (7934113401022441849 / 4000000000000000000) (by norm_num) (by norm_num) (by norm_num)
  have hbudget : e0 < (1 / 10 ^ 32 : ℝ) := by
    norm_num [e0, manuscriptTermRoundStep]
  change |(manuscriptCase1X0SubstituteRat : ℝ) - (manuscriptCase1X0RoundedSubstituteRat : ℝ)| ≤ e0 at h0
  exact h0.trans_lt hbudget

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan

theorem manuscript_case1X0_actual_substitution_error :
    |barrierCase1X (Case1PointData.X0 : ℝ) - (manuscriptCase1X0SubstituteRat : ℝ)| < ((35 / 1000000000000000) : ℝ) := by
  have hw : manuscriptCase1X0Interval.2 - manuscriptCase1X0Interval.1 < ((35 / 1000000000000000) : ℚ) :=
    manuscript_case1X0_interval_width.trans (by norm_num)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using manuscript_interval_abs_sub_lt_of_width
    manuscriptCase1X0Interval.1 manuscriptCase1X0Interval.2 manuscriptCase1X0SubstituteRat
    (barrierCase1X (Case1PointData.X0 : ℝ)) (35 / 1000000000000000)
    manuscript_case1X0_interval manuscript_case1X0_substitute_interval hw

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def manuscriptCase1X1RoundedSubstituteRat : ℚ :=
  manuscriptRoundedXFieldRat (41 / 48) (barrierCase1XRat Case1PointData.X1) (-3) (0) (0) (2259572153 / 1250000000) (12259572153 / 10000000000) (105105666314613055409 / 100000000000000000000)

theorem manuscript_case1X1_additional_rounding_error :
    |(manuscriptCase1X1SubstituteRat : ℝ) - (manuscriptCase1X1RoundedSubstituteRat : ℝ)| < (1 / 10 ^ 32 : ℝ) := by
  let a0 : ℚ := barrierCase1XApproxRat Case1PointData.X1 (-3) (0) (0) (2259572153 / 1250000000) (12259572153 / 10000000000) (105105666314613055409 / 100000000000000000000)
  let r0 : ℚ := manuscriptRoundedXFieldRat (41 / 48) (barrierCase1XRat Case1PointData.X1) (-3) (0) (0) (2259572153 / 1250000000) (12259572153 / 10000000000) (105105666314613055409 / 100000000000000000000)
  let e0 : ℝ := ((19 / 48 : ℝ) + 1 / 12 + |(((41 / 48) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  have h0 : |(a0 : ℝ) - (r0 : ℝ)| ≤ e0 := by
    exact manuscript_rounded_x_field_error_le (41 / 48) (barrierCase1XRat Case1PointData.X1) (-3) (0) (0) (2259572153 / 1250000000) (12259572153 / 10000000000) (105105666314613055409 / 100000000000000000000) (by norm_num) (by norm_num) (by norm_num)
  have hbudget : e0 < (1 / 10 ^ 32 : ℝ) := by
    norm_num [e0, manuscriptTermRoundStep]
  change |(manuscriptCase1X1SubstituteRat : ℝ) - (manuscriptCase1X1RoundedSubstituteRat : ℝ)| ≤ e0 at h0
  exact h0.trans_lt hbudget

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan

theorem manuscript_case1X1_actual_substitution_error :
    |barrierCase1X (Case1PointData.X1 : ℝ) - (manuscriptCase1X1SubstituteRat : ℝ)| < ((35 / 1000000000000000) : ℝ) := by
  have hw : manuscriptCase1X1Interval.2 - manuscriptCase1X1Interval.1 < ((35 / 1000000000000000) : ℚ) :=
    manuscript_case1X1_interval_width.trans (by norm_num)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using manuscript_interval_abs_sub_lt_of_width
    manuscriptCase1X1Interval.1 manuscriptCase1X1Interval.2 manuscriptCase1X1SubstituteRat
    (barrierCase1X (Case1PointData.X1 : ℝ)) (35 / 1000000000000000)
    manuscript_case1X1_interval manuscript_case1X1_substitute_interval hw

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def manuscriptCase1X2RoundedSubstituteRat : ℚ :=
  manuscriptRoundedXFieldRat (41 / 48) (barrierCase1XRat Case1PointData.X2) (-2) (-1) (0) (1271904013 / 1250000000) (3728095987 / 2500000000) (26617739818285504169 / 25000000000000000000)

theorem manuscript_case1X2_additional_rounding_error :
    |(manuscriptCase1X2SubstituteRat : ℝ) - (manuscriptCase1X2RoundedSubstituteRat : ℝ)| < (1 / 10 ^ 32 : ℝ) := by
  let a0 : ℚ := barrierCase1XApproxRat Case1PointData.X2 (-2) (-1) (0) (1271904013 / 1250000000) (3728095987 / 2500000000) (26617739818285504169 / 25000000000000000000)
  let r0 : ℚ := manuscriptRoundedXFieldRat (41 / 48) (barrierCase1XRat Case1PointData.X2) (-2) (-1) (0) (1271904013 / 1250000000) (3728095987 / 2500000000) (26617739818285504169 / 25000000000000000000)
  let e0 : ℝ := ((19 / 48 : ℝ) + 1 / 12 + |(((41 / 48) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  have h0 : |(a0 : ℝ) - (r0 : ℝ)| ≤ e0 := by
    exact manuscript_rounded_x_field_error_le (41 / 48) (barrierCase1XRat Case1PointData.X2) (-2) (-1) (0) (1271904013 / 1250000000) (3728095987 / 2500000000) (26617739818285504169 / 25000000000000000000) (by norm_num) (by norm_num) (by norm_num)
  have hbudget : e0 < (1 / 10 ^ 32 : ℝ) := by
    norm_num [e0, manuscriptTermRoundStep]
  change |(manuscriptCase1X2SubstituteRat : ℝ) - (manuscriptCase1X2RoundedSubstituteRat : ℝ)| ≤ e0 at h0
  exact h0.trans_lt hbudget

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan

theorem manuscript_case1X2_actual_substitution_error :
    |barrierCase1X (Case1PointData.X2 : ℝ) - (manuscriptCase1X2SubstituteRat : ℝ)| < ((35 / 1000000000000000) : ℝ) := by
  have hw : manuscriptCase1X2Interval.2 - manuscriptCase1X2Interval.1 < ((35 / 1000000000000000) : ℚ) :=
    manuscript_case1X2_interval_width.trans (by norm_num)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using manuscript_interval_abs_sub_lt_of_width
    manuscriptCase1X2Interval.1 manuscriptCase1X2Interval.2 manuscriptCase1X2SubstituteRat
    (barrierCase1X (Case1PointData.X2 : ℝ)) (35 / 1000000000000000)
    manuscript_case1X2_interval manuscript_case1X2_substitute_interval hw

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def manuscriptCase1X3RoundedSubstituteRat : ℚ :=
  manuscriptRoundedXFieldRat (41 / 48) (barrierCase1XRat Case1PointData.X3) (-2) (-1) (0) (4437270259 / 2500000000) (5562729741 / 5000000000) (119689367351405927081 / 100000000000000000000)

theorem manuscript_case1X3_additional_rounding_error :
    |(manuscriptCase1X3SubstituteRat : ℝ) - (manuscriptCase1X3RoundedSubstituteRat : ℝ)| < (1 / 10 ^ 32 : ℝ) := by
  let a0 : ℚ := barrierCase1XApproxRat Case1PointData.X3 (-2) (-1) (0) (4437270259 / 2500000000) (5562729741 / 5000000000) (119689367351405927081 / 100000000000000000000)
  let r0 : ℚ := manuscriptRoundedXFieldRat (41 / 48) (barrierCase1XRat Case1PointData.X3) (-2) (-1) (0) (4437270259 / 2500000000) (5562729741 / 5000000000) (119689367351405927081 / 100000000000000000000)
  let e0 : ℝ := ((19 / 48 : ℝ) + 1 / 12 + |(((41 / 48) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  have h0 : |(a0 : ℝ) - (r0 : ℝ)| ≤ e0 := by
    exact manuscript_rounded_x_field_error_le (41 / 48) (barrierCase1XRat Case1PointData.X3) (-2) (-1) (0) (4437270259 / 2500000000) (5562729741 / 5000000000) (119689367351405927081 / 100000000000000000000) (by norm_num) (by norm_num) (by norm_num)
  have hbudget : e0 < (1 / 10 ^ 32 : ℝ) := by
    norm_num [e0, manuscriptTermRoundStep]
  change |(manuscriptCase1X3SubstituteRat : ℝ) - (manuscriptCase1X3RoundedSubstituteRat : ℝ)| ≤ e0 at h0
  exact h0.trans_lt hbudget

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan

theorem manuscript_case1X3_actual_substitution_error :
    |barrierCase1X (Case1PointData.X3 : ℝ) - (manuscriptCase1X3SubstituteRat : ℝ)| < ((35 / 1000000000000000) : ℝ) := by
  have hw : manuscriptCase1X3Interval.2 - manuscriptCase1X3Interval.1 < ((35 / 1000000000000000) : ℚ) :=
    manuscript_case1X3_interval_width.trans (by norm_num)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using manuscript_interval_abs_sub_lt_of_width
    manuscriptCase1X3Interval.1 manuscriptCase1X3Interval.2 manuscriptCase1X3SubstituteRat
    (barrierCase1X (Case1PointData.X3 : ℝ)) (35 / 1000000000000000)
    manuscript_case1X3_interval manuscript_case1X3_substitute_interval hw

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def manuscriptCase1X4RoundedSubstituteRat : ℚ :=
  manuscriptRoundedXFieldRat (41 / 48) (barrierCase1XRat Case1PointData.X4) (-1) (-2) (0) (634829897 / 500000000) (365170103 / 250000000) (1403008998125030609 / 1000000000000000000)

theorem manuscript_case1X4_additional_rounding_error :
    |(manuscriptCase1X4SubstituteRat : ℝ) - (manuscriptCase1X4RoundedSubstituteRat : ℝ)| < (1 / 10 ^ 32 : ℝ) := by
  let a0 : ℚ := barrierCase1XApproxRat Case1PointData.X4 (-1) (-2) (0) (634829897 / 500000000) (365170103 / 250000000) (1403008998125030609 / 1000000000000000000)
  let r0 : ℚ := manuscriptRoundedXFieldRat (41 / 48) (barrierCase1XRat Case1PointData.X4) (-1) (-2) (0) (634829897 / 500000000) (365170103 / 250000000) (1403008998125030609 / 1000000000000000000)
  let e0 : ℝ := ((19 / 48 : ℝ) + 1 / 12 + |(((41 / 48) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  have h0 : |(a0 : ℝ) - (r0 : ℝ)| ≤ e0 := by
    exact manuscript_rounded_x_field_error_le (41 / 48) (barrierCase1XRat Case1PointData.X4) (-1) (-2) (0) (634829897 / 500000000) (365170103 / 250000000) (1403008998125030609 / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num)
  have hbudget : e0 < (1 / 10 ^ 32 : ℝ) := by
    norm_num [e0, manuscriptTermRoundStep]
  change |(manuscriptCase1X4SubstituteRat : ℝ) - (manuscriptCase1X4RoundedSubstituteRat : ℝ)| ≤ e0 at h0
  exact h0.trans_lt hbudget

end InternalCatalan

end

end

end OAI
