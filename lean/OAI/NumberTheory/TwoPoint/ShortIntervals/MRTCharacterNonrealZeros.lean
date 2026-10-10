import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterHighZeros

namespace OAI

/-! Characters whose square is nonprincipal have a classical zero-free
strip at every height. The real quadratic exceptional-zero case is excluded
explicitly by the square-character hypothesis. -/

namespace TwoPointCorrelations

open Complex
open scoped Classical

theorem mrt_character_nonreal_zero_free : ∃ c : ℝ, 0 < c ∧
    ∀ (q : ℕ) [NeZero q], ∀ (χ : DirichletCharacter ℂ q), χ ^ 2 ≠ 1 →
    ∀ t beta : ℝ, 1 - c / mrtCharacterHeight q t ≤ beta →
      DirichletCharacter.LFunction χ ((beta : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
  obtain ⟨C, hC, hchar⟩ := mrt_character_logderiv_growth_constant
  obtain ⟨delta0, hd0, Z, hZ, hzeta⟩ := Erdos970.uniform_bound_Z0
  let D := 6 * Z + 6 * C + 1 + 2 / delta0
  have hD1 : 1 ≤ D := by
    have hdiv : 0 ≤ 2 / delta0 := by positivity
    dsimp only [D]
    linarith
  have hD : 0 < D := zero_lt_one.trans_le hD1
  have hDdelta : 2 ≤ delta0 * D := by
    have he : delta0 * (2 / delta0) = 2 := by field_simp
    have hm : 0 ≤ delta0 * (6 * Z + 6 * C + 1) := by positivity
    dsimp only [D]
    nlinarith only [he, hm]
  let b := 1 / (10 * D)
  have hb : 0 < b := by dsimp [b]; positivity
  have hbsmall : b ≤ 1 / 10 := by
    dsimp [b]
    apply (div_le_iff₀ (by positivity : 0 < 10 * D)).mpr
    linarith
  have hbdelta : b < delta0 / 4 := by
    dsimp [b]
    apply (div_lt_iff₀ (by positivity : 0 < 10 * D)).mpr
    nlinarith [hDdelta]
  refine ⟨b / 4, by positivity, ?_⟩
  intro q _ χ hχ2 t beta hbeta hzero
  have hχ : χ ≠ 1 := by intro he; simp [he] at hχ2
  let H := mrtCharacterHeight q t
  have hHhalf : 1 / 2 ≤ H := by
    have hlog2 : 1 / 2 ≤ Real.log 2 := by
      have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hh ⊢
      exact hh
    exact hlog2.trans ((Real.log_le_log (by norm_num)
      (by linarith [abs_nonneg t])).trans (mrt_character_height_ge q t))
  have hH : 0 < H := lt_of_lt_of_le (by norm_num) hHhalf
  let delta := b / H
  have hd : 0 < delta := div_pos hb hH
  have hdsmall : delta ≤ 2 * b := by
    apply (div_le_iff₀ hH).mpr
    nlinarith
  have hd1 : delta < 1 := by linarith
  have hdelta0 : delta < delta0 := by linarith
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
  have hs0 := (hchar q (χ ^ 2) hχ2 (2 * t) (1 + delta)
    (by linarith) (by linarith)).1
  have hh := mul_le_mul_of_nonneg_left (mrt_character_height_double q t) hC.le
  have hs : (-deriv (DirichletCharacter.LFunction (χ ^ 2))
      ((1 + delta : ℝ) + Complex.I * ((2 * t : ℝ) : ℂ)) /
      DirichletCharacter.LFunction (χ ^ 2)
        ((1 + delta : ℝ) + Complex.I * ((2 * t : ℝ) : ℂ))).re ≤ 2 * C * H := by
    calc
      _ ≤ C * (2 * H) := hs0.trans hh
      _ = _ := by ring
  have hz := hzeta delta hd hdelta0
  have hp := mrtCharacter_logderiv_positivity χ (σ := 1 + delta) (by linarith) t
  have hpoint : ((1 + delta : ℝ) : ℂ) = (1 : ℂ) + (delta : ℂ) := by push_cast; rfl
  simp only [Erdos970.logDerivZeta, ← neg_div] at hz
  rw [← hpoint] at hz
  have hdist : 1 + delta - beta = delta + eps := by dsimp [eps]; ring
  rw [hdist] at hc
  have hcost : 3 * Z + 6 * C * H ≤ D * H := by
    have hZm := mul_nonneg hZ (show 0 ≤ 2 * H - 1 by linarith)
    have hdm : 0 ≤ (2 / delta0) * H := by positivity
    dsimp only [D]
    nlinarith
  have hpos : 0 ≤ 3 / delta + D * H - 4 / (delta + eps) := by
    have hm := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hz (by norm_num : (0 : ℝ) ≤ 3))
        (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 4))) hs
    have hexp : 3 * (1 / delta + Z) +
        4 * (C * mrtCharacterHeight q t - 1 / (delta + eps)) + 2 * C * H =
        3 / delta + (3 * Z + 6 * C * H) - 4 / (delta + eps) := by
      dsimp only [H]
      ring
    rw [hexp] at hm
    have hbound := hp.trans hm
    linarith only [hbound, hcost]
  have hdeq : delta = 1 / (10 * D * H) := by
    change (1 / (10 * D)) / H = 1 / (10 * D * H)
    field_simp
  exact (not_lt_of_ge hpos) (mrt_character_zero_free_arithmetic hD hH hdeq he heu)

end TwoPointCorrelations

end OAI
