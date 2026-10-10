import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterLogGrowth
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrincipalCorrection
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterPositivity
import StrongPNT.Erdos970.PNT4_ZeroFreeRegion

namespace OAI

/-! A classical logarithmic zero-free strip, uniform in the character modulus.
This is the high-height part only; it makes no Vinogradov--Korobov claim. -/

namespace TwoPointCorrelations

open Complex
open scoped Classical

lemma mrt_character_principal_neg_logderiv_re {q : ℕ} [NeZero q]
    {s : ℂ} (hs : 1 < s.re) :
    (-deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s /
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s).re ≤
        (-deriv riemannZeta s / riemannZeta s).re + Real.log (q : ℝ) := by
  have h := (Complex.abs_re_le_norm _).trans (mrt_principal_logderiv_error (q := q) hs)
  rw [Complex.sub_re] at h
  have := (abs_le.mp h).1
  simp only [logDeriv_apply] at this
  simp only [neg_div, Complex.neg_re]
  linarith

lemma mrt_character_square_logderiv_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℕ) [NeZero q], ∀ (χ : DirichletCharacter ℂ q) (t delta : ℝ),
      2 < |t| → 0 < delta → delta < 1 →
      (-deriv (DirichletCharacter.LFunction (χ ^ 2))
          ((1 + delta : ℝ) + Complex.I * ((2 * t : ℝ) : ℂ)) /
        DirichletCharacter.LFunction (χ ^ 2)
          ((1 + delta : ℝ) + Complex.I * ((2 * t : ℝ) : ℂ))).re ≤
            C * mrtCharacterHeight q t := by
  obtain ⟨C, hC, hchar⟩ := mrt_character_logderiv_growth_constant
  obtain ⟨Z, hZ, hzeta⟩ := Erdos970.lem_Z2bound
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  refine ⟨2 * C + Z + 1, by linarith, ?_⟩
  intro q _ χ t delta ht hd hd1
  have hH : 0 < mrtCharacterHeight q t := mrt_character_height_pos q t
  by_cases hχ : χ ^ 2 = 1
  · rw [hχ]
    let s : ℂ := ((1 + delta : ℝ) : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ)
    have hs : 1 < s.re := by dsimp [s]; norm_num; linarith
    have hp := mrt_character_principal_neg_logderiv_re (q := q) hs
    have hz := hzeta t ht delta ⟨hd, hd1⟩
    have hpoint : s = (1 : ℂ) + (delta : ℂ) + 2 * (t : ℂ) * Complex.I := by
      dsimp [s]
      push_cast
      ring
    simp only [Erdos970.logDerivZeta, ← neg_div] at hz
    rw [← hpoint] at hz
    have hz' := mul_le_mul_of_nonneg_left (mrt_character_height_ge q t) hZ0.le
    have hq := mrt_character_log_modulus_le_height q t
    change _ ≤ (2 * C + Z + 1) * mrtCharacterHeight q t
    linarith [mul_pos hC hH]
  · have hc := (hchar q (χ ^ 2) hχ (2 * t) (1 + delta)
      (by linarith) (by linarith)).1
    have hm := mul_le_mul_of_nonneg_left (mrt_character_height_double q t) hC.le
    linarith [mul_pos hZ0 hH]

lemma mrt_character_zero_free_arithmetic {D H delta eps : ℝ}
    (hD : 0 < D) (hH : 0 < H) (hd : delta = 1 / (10 * D * H))
    (he : 0 ≤ eps) (heu : eps ≤ delta / 4) :
    3 / delta + D * H - 4 / (delta + eps) < 0 := by
  have hdp : 0 < delta := by rw [hd]; positivity
  have hde : 0 < delta + eps := by linarith
  have hinv : 16 / (5 * delta) ≤ 4 / (delta + eps) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 5 * delta) hde).mpr
    nlinarith
  have heq : 3 / delta + D * H - 16 / (5 * delta) = -(D * H) := by
    rw [hd]
    field_simp [hD.ne', hH.ne']
    ring
  have hle : 3 / delta + D * H - 4 / (delta + eps) ≤
      3 / delta + D * H - 16 / (5 * delta) := by linarith
  rw [heq] at hle
  exact hle.trans_lt (neg_neg_of_pos (mul_pos hD hH))

/-- Absolute constants give the usual logarithmic strip at high height,
uniformly over all positive moduli and nonprincipal characters. -/
theorem mrt_character_nonprincipal_high_zero_free : ∃ c : ℝ, 0 < c ∧
    ∃ T : ℝ, 2 < T ∧ ∀ (q : ℕ) [NeZero q],
    ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ (t beta : ℝ), T ≤ |t| →
      1 - c / mrtCharacterHeight q t ≤ beta →
      DirichletCharacter.LFunction χ ((beta : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
  obtain ⟨C, hC, hchar⟩ := mrt_character_logderiv_growth_constant
  obtain ⟨S, hS, hsquare⟩ := mrt_character_square_logderiv_bound
  obtain ⟨delta0, hd0, Z, hZ, hzeta⟩ := Erdos970.uniform_bound_Z0
  let D := 3 * Z + 4 * C + S + 1
  have hD1 : 1 ≤ D := by dsimp [D]; linarith
  have hD : 0 < D := zero_lt_one.trans_le hD1
  let b := 1 / (10 * D)
  have hb : 0 < b := by dsimp [b]; positivity
  have hbsmall : b ≤ 1 / 10 := by
    dsimp [b]
    apply (div_le_iff₀ (by positivity : 0 < 10 * D)).mpr
    linarith
  let T := Real.exp (1 + b / delta0) + 3
  have hT : 2 < T := by dsimp [T]; linarith [Real.exp_pos (1 + b / delta0)]
  refine ⟨b / 4, by positivity, T, hT, ?_⟩
  intro q _ χ hχ t beta ht hbeta hzero
  have ht2 : 2 < |t| := hT.trans_le ht
  let H := mrtCharacterHeight q t
  have hHlarge : 1 + b / delta0 < H := by
    apply lt_of_lt_of_le _ (mrt_character_height_ge q t)
    apply (Real.lt_log_iff_exp_lt (by positivity : 0 < |t| + 2)).mpr
    dsimp [T] at ht
    linarith
  have hH1 : 1 < H := by have := div_pos hb hd0; linarith
  have hH : 0 < H := zero_lt_one.trans hH1
  let delta := b / H
  have hd : 0 < delta := div_pos hb hH
  have hdsmall : delta ≤ b := by
    apply (div_le_iff₀ hH).mpr
    nlinarith
  have hd1 : delta < 1 := by linarith
  have hdelta0 : delta < delta0 := by
    apply (div_lt_iff₀ hH).mpr
    have hm := (div_lt_iff₀ hd0).mp (show b / delta0 < H by linarith)
    simpa only [mul_comm] using hm
  have hbeta1 : beta < 1 := by
    by_contra! h
    exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by simpa using h) hzero
  let eps := 1 - beta
  have he : 0 ≤ eps := by dsimp [eps]; linarith
  have heu : eps ≤ delta / 4 := by
    change 1 - (b / 4) / H ≤ beta at hbeta
    have heq : (b / 4) / H = (b / H) / 4 := by ring
    rw [heq] at hbeta
    dsimp only [eps, delta]
    linarith
  have hbetalow : 3 / 4 ≤ beta := by dsimp [eps] at heu; linarith
  have hc := (hchar q χ hχ t (1 + delta) (by linarith) (by linarith)).2
    beta hbetalow hbeta1.le hzero
  have hs := hsquare q χ t delta ht2 hd hd1
  have hz := hzeta delta hd hdelta0
  have hp := mrtCharacter_logderiv_positivity χ (σ := 1 + delta) (by linarith) t
  have hpoint : ((1 + delta : ℝ) : ℂ) = (1 : ℂ) + (delta : ℂ) := by push_cast; rfl
  simp only [Erdos970.logDerivZeta, ← neg_div] at hz
  rw [← hpoint] at hz
  have hdist : 1 + delta - beta = delta + eps := by dsimp [eps]; ring
  rw [hdist] at hc
  have hcost : 3 * Z + (4 * C + S) * H ≤ D * H := by
    dsimp [D]
    nlinarith [mul_nonneg hZ (show 0 ≤ H - 1 by linarith)]
  have hpos : 0 ≤ 3 / delta + D * H - 4 / (delta + eps) := by
    have hm := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hz (by norm_num : (0 : ℝ) ≤ 3))
        (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 4))) hs
    have hexp : 3 * (1 / delta + Z) +
        4 * (C * mrtCharacterHeight q t - 1 / (delta + eps)) +
        S * mrtCharacterHeight q t =
        3 / delta + (3 * Z + (4 * C + S) * H) - 4 / (delta + eps) := by
      dsimp only [H]
      ring
    rw [hexp] at hm
    have hh := hp.trans hm
    linarith only [hh, hcost]
  have hdeq : delta = 1 / (10 * D * H) := by
    change (1 / (10 * D)) / H = 1 / (10 * D * H)
    field_simp
  exact (not_lt_of_ge hpos) (mrt_character_zero_free_arithmetic hD hH hdeq he heu)

end TwoPointCorrelations

end OAI
