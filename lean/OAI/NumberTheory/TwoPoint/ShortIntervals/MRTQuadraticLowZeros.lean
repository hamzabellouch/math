import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTQuadraticDisk
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTZetaPole

namespace OAI

/-! The effective quadratic disk supplies the bounded-height part of a
zero-free strip, with its polynomial modulus dependence displayed. -/

namespace TwoPointCorrelations

open Complex
open scoped Classical

lemma mrt_character_height_half (q : ℕ) [NeZero q] (t : ℝ) :
    (1 / 2 : ℝ) ≤ mrtCharacterHeight q t := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  exact hlog2.trans ((Real.log_le_log (by norm_num)
    (by linarith [abs_nonneg t])).trans (mrt_character_height_ge q t))

lemma mrt_real_shift_norm {delta t : ℝ} (hd : 0 ≤ delta) :
    ‖((1 + delta : ℝ) : ℂ) + Complex.I * (t : ℂ)‖ ≤ 1 + delta + |t| := by
  calc
    _ ≤ |(((1 + delta : ℝ) : ℂ) + Complex.I * (t : ℂ)).re| +
        |(((1 + delta : ℝ) : ℂ) + Complex.I * (t : ℂ)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = _ := by simp [abs_of_nonneg (show 0 ≤ 1 + delta by linarith)]

lemma mrt_real_shift_inv_norm {delta t : ℝ} (ht : t ≠ 0) :
    ‖((((1 + delta : ℝ) : ℂ) + Complex.I * (t : ℂ)) - 1)⁻¹‖ ≤ 1 / |t| := by
  rw [norm_inv, one_div]
  apply inv_anti₀ (abs_pos.mpr ht)
  have hh := Complex.abs_im_le_norm
    ((((1 + delta : ℝ) : ℂ) + Complex.I * (t : ℂ)) - 1)
  simpa using hh

lemma mrt_quadratic_zero_cost {C Z Q H : ℝ}
    (hC : 0 ≤ C) (hZ : 0 ≤ Z) (hQ : 1 ≤ Q) (hH : 1 / 2 ≤ H) :
    4 * Z + 4 * C * H + 3072 * Q + H ≤ (8 * Z + 4 * C + 6200) * (Q * H) := by
  have hH0 : 0 ≤ H := le_trans (by norm_num) hH
  have hQH : H ≤ Q * H := by nlinarith only [hQ, hH0]
  have hQHhalf : 1 / 2 ≤ Q * H := hH.trans hQH
  have hCH := mul_le_mul_of_nonneg_left hQH hC
  have hZH := mul_le_mul_of_nonneg_left hQHhalf hZ
  have hQH' : Q ≤ 2 * (Q * H) := by nlinarith only [hH, hQ]
  nlinarith only [hQH, hQHhalf, hCH, hZH, hQH']

lemma mrt_quadratic_zero_combine {a b d Z C Q H delta eps D : ℝ}
    (hpos : 0 ≤ 3 * a + 4 * b + d)
    (ha : a ≤ Z + 1 / delta) (hb : b ≤ C * H - 1 / (delta + eps))
    (hd : d ≤ Z + 3072 * Q + H)
    (hcost : 4 * Z + 4 * C * H + 3072 * Q + H ≤ D * (Q * H)) :
    0 ≤ 3 / delta + D * (Q * H) - 4 / (delta + eps) := by
  calc
    0 ≤ 3 * a + 4 * b + d := hpos
    _ ≤ 3 * (Z + 1 / delta) + 4 * (C * H - 1 / (delta + eps)) +
        (Z + 3072 * Q + H) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left ha (by norm_num))
        (mul_le_mul_of_nonneg_left hb (by norm_num))) hd
    _ = 3 / delta + (4 * Z + 4 * C * H + 3072 * Q + H) -
        4 / (delta + eps) := by ring
    _ ≤ 3 / delta + D * (Q * H) - 4 / (delta + eps) :=
      sub_le_sub_right (add_le_add_right hcost _) _

/-- The constant can depend on the fixed height cutoff, but not the modulus. -/
theorem mrt_quadratic_bounded_height_zero_free (T : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q],
      ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 →
      ∀ t beta : ℝ, |t| ≤ T →
        1 - c / ((q : ℝ) ^ 2 * mrtCharacterHeight q t) ≤ beta →
        DirichletCharacter.LFunction χ ((beta : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
  obtain ⟨C, hC, hchar⟩ := mrt_character_logderiv_growth_constant
  obtain ⟨Z, hZ, hzeta⟩ := mrt_zeta_neg_logderiv_bounded (2 * |T| + 3)
  let D := 8 * Z + 4 * C + 6200
  have hDlarge : 6200 ≤ D := by dsimp [D]; linarith
  have hD : 0 < D := by linarith
  let b := 1 / (10 * D)
  have hb : 0 < b := by dsimp [b]; positivity
  refine ⟨b / 4, by positivity, ?_⟩
  intro q _ χ hχ hχsq t beta ht hbeta hzero
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : 0 < (q : ℝ) := lt_of_lt_of_le zero_lt_one hq
  let Q : ℝ := (q : ℝ) ^ 2
  have hQ : 1 ≤ Q := by dsimp [Q]; nlinarith only [hq]
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  let H := mrtCharacterHeight q t
  have hHhalf : (1 / 2 : ℝ) ≤ H := mrt_character_height_half q t
  have hH : 0 < H := lt_of_lt_of_le (by norm_num) hHhalf
  let delta := b / (Q * H)
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hdeq : delta = 1 / (10 * D * (Q * H)) := by dsimp [delta, b]; field_simp
  have hdsmall : delta ≤ 1 / (3072 * Q) := by
    rw [hdeq]
    apply one_div_le_one_div_of_le (by positivity)
    have hDH : 3072 ≤ 10 * D * H := by
      nlinarith only [hDlarge, hHhalf,
        mul_nonneg (show 0 ≤ D - 6200 by linarith only [hDlarge])
          (show 0 ≤ H - 1 / 2 by linarith only [hHhalf])]
    have hm := mul_le_mul_of_nonneg_right hDH hQ0.le
    nlinarith only [hm]
  have hd1 : delta < 1 := by
    have hh : 1 / (3072 * Q) ≤ (1 / 3072 : ℝ) := by
      apply (div_le_iff₀ (by positivity : 0 < 3072 * Q)).mpr
      nlinarith
    linarith
  have hbeta1 : beta < 1 := by
    by_contra! h
    exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by simpa using h) hzero
  let eps := 1 - beta
  have he : 0 ≤ eps := by dsimp [eps]; linarith
  have heu : eps ≤ delta / 4 := by
    change 1 - (b / 4) / (Q * H) ≤ beta at hbeta
    have heq : (b / 4) / (Q * H) = (b / (Q * H)) / 4 := by ring
    rw [heq] at hbeta
    dsimp only [eps, delta]
    linarith
  by_cases htiny : |t| ≤ 1 / (3072 * Q)
  · apply mrt_quadratic_near_one_nonzero χ hχ hχsq (s := (beta : ℂ) + I * (t : ℂ)) _ hzero
    have hn := Complex.norm_le_abs_re_add_abs_im ((beta : ℂ) + I * (t : ℂ) - 1)
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
      sub_zero, add_zero, Complex.one_re, Complex.sub_im, Complex.add_im,
      Complex.mul_im, zero_add, one_mul, Complex.one_im] at hn
    rw [abs_of_nonpos (by linarith : beta - 1 ≤ 0)] at hn
    have htwice : 2 * (1 / (3072 * Q)) = 1 / (1536 * Q) := by
      field_simp
      norm_num
    change ‖(beta : ℂ) + I * (t : ℂ) - 1‖ ≤ 1 / (1536 * Q)
    dsimp only [eps] at heu
    have hrpos : 0 ≤ 1 / (3072 * Q) := by positivity
    linarith only [hn, heu, htiny, hdsmall, htwice, hrpos]
  have ht0 : t ≠ 0 := by
    intro heq
    apply htiny
    rw [heq, abs_zero]
    positivity
  have hlarge : 1 / |2 * t| ≤ 3072 * Q := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply (div_le_iff₀ (by positivity : 0 < 2 * |t|)).mpr
    have hu := (div_lt_iff₀ (by positivity : 0 < 3072 * Q)).mp (lt_of_not_ge htiny)
    nlinarith only [hu]
  have hnorm0 : ‖((1 + delta : ℝ) : ℂ)‖ ≤ 2 * |T| + 3 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 + delta)]
    linarith [abs_nonneg T]
  have hz := hzeta ((1 + delta : ℝ) : ℂ) (by simp; linarith) hnorm0 (by
    intro heq; have := congrArg Complex.re heq; simp at this; linarith)
  have hinv : ‖(((1 + delta : ℝ) : ℂ) - 1)⁻¹‖ = 1 / delta := by
    rw [show ((1 + delta : ℝ) : ℂ) - 1 = (delta : ℂ) by push_cast; ring]
    simp [norm_inv, abs_of_pos hd, one_div]
  rw [hinv] at hz
  let s₂ : ℂ := ((1 + delta : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ)
  have hs₂ : 1 < s₂.re := by dsimp [s₂]; simp; linarith
  have hnorm₂ : ‖s₂‖ ≤ 2 * |T| + 3 := by
    have hh := mrt_real_shift_norm (t := 2 * t) hd.le
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
    have htt := ht.trans (le_abs_self T)
    dsimp only [s₂]
    linarith
  have hz₂ := hzeta s₂ hs₂.le hnorm₂ (by intro h; rw [h] at hs₂; norm_num at hs₂)
  have hi₂ := mrt_real_shift_inv_norm (delta := delta)
    (show (2 * t : ℝ) ≠ 0 from mul_ne_zero (by norm_num) ht0)
  have hp₂ := mrt_character_principal_neg_logderiv_re (q := q) hs₂
  have hsquare : (-deriv (DirichletCharacter.LFunction (χ ^ 2)) s₂ /
      DirichletCharacter.LFunction (χ ^ 2) s₂).re ≤ Z + 3072 * Q + H := by
    rw [hχsq]
    have hlogq := mrt_character_log_modulus_le_height q t
    change _ ≤ Z + 3072 * Q + mrtCharacterHeight q t
    dsimp only [s₂] at hz₂ hp₂ ⊢
    linarith
  have hbetalow : 3 / 4 ≤ beta := by dsimp [eps] at heu; linarith
  have hc := (hchar q χ hχ t (1 + delta) (by linarith) (by linarith)).2
    beta hbetalow hbeta1.le hzero
  have hdist : 1 + delta - beta = delta + eps := by dsimp [eps]; ring
  rw [hdist] at hc
  have hp := mrtCharacter_logderiv_positivity χ (σ := 1 + delta) (by linarith) t
  have hcost : 4 * Z + 4 * C * H + 3072 * Q + H ≤ D * (Q * H) :=
    mrt_quadratic_zero_cost hC.le hZ hQ hHhalf
  have hpos : 0 ≤ 3 / delta + D * (Q * H) - 4 / (delta + eps) := by
    exact mrt_quadratic_zero_combine hp hz hc hsquare hcost

  exact (not_lt_of_ge hpos)
    (mrt_character_zero_free_arithmetic hD (mul_pos hQ0 hH) hdeq he heu)

end TwoPointCorrelations

end OAI
