import OAI.NumberTheory.TwoPointCorrelations.ModFiveLogGrowth
import OAI.NumberTheory.TwoPointCorrelations.ModFivePrincipalCorrection
import StrongPNT.Erdos970.PNT4_ZeroFreeRegion

namespace OAI

/-! The high-height logarithmic zero-free strip for nonprincipal characters
modulo five. The zeta estimates are existing proved theorems; all character
estimates come from the finite-period Abel bounds and the disk expansion.
-/

namespace TwoPointCorrelations

open Complex
open scoped Classical

lemma modFive_principal_neg_logderiv_re {s : ℂ} (hs : 1 < s.re) :
    (-deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 5)) s /
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 5) s).re ≤
        (-deriv riemannZeta s / riemannZeta s).re + Real.log 5 / 4 := by
  have h := (Complex.abs_re_le_norm _).trans (modFive_principal_logderiv_error hs)
  rw [Complex.sub_re] at h
  have := (abs_le.mp h).2
  linarith

lemma modFive_square_logderiv_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : DirichletCharacter ℂ 5) (t δ : ℝ), 2 < |t| → 0 < δ → δ < 1 →
      (-deriv (DirichletCharacter.LFunction (χ ^ 2))
          ((1 + δ : ℝ) + Complex.I * ((2 * t : ℝ) : ℂ)) /
        DirichletCharacter.LFunction (χ ^ 2)
          ((1 + δ : ℝ) + Complex.I * ((2 * t : ℝ) : ℂ))).re ≤
            C * Real.log (|t| + 2) := by
  obtain ⟨C, hC, hchar⟩ := modFive_logderiv_growth_constant
  obtain ⟨Z, hZ, hzeta⟩ := Erdos970.lem_Z2bound
  let A := Real.log 5 / (4 * Real.log 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨2 * C + Z + A + 1, by linarith, ?_⟩
  intro χ t δ ht hδ hδ1
  have hH : 0 < Real.log (|t| + 2) := modFive_log_height_pos t
  by_cases hχ : χ ^ 2 = 1
  · rw [hχ]
    let s : ℂ := ((1 + δ : ℝ) : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ)
    have hs : 1 < s.re := by dsimp [s]; norm_num; linarith
    have hp := modFive_principal_neg_logderiv_re hs
    have hz := hzeta t ht δ ⟨hδ, hδ1⟩
    have hpoint : s = (1 : ℂ) + (δ : ℂ) + 2 * (t : ℂ) * Complex.I := by
      dsimp [s]
      push_cast
      ring
    simp only [Erdos970.logDerivZeta, ← neg_div] at hz
    rw [← hpoint] at hz
    have ha : Real.log 5 / 4 ≤ A * Real.log (|t| + 2) := by
      have hl : Real.log 2 ≤ Real.log (|t| + 2) :=
        Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
      have hm := mul_le_mul_of_nonneg_left hl hA
      have he : A * Real.log 2 = Real.log 5 / 4 := by dsimp [A]; field_simp
      rw [he] at hm
      exact hm
    change _ ≤ (2 * C + Z + A + 1) * Real.log (|t| + 2)
    linarith [mul_pos hC hH]
  · have hc := (hchar (χ ^ 2) hχ (2 * t) (1 + δ) (by linarith) (by linarith)).1
    have hd := modFive_log_double_height t
    have hm := mul_le_mul_of_nonneg_left hd hC.le
    linarith [mul_pos (show 0 < Z by linarith) hH, mul_nonneg hA hH.le]

lemma modFive_zero_free_arithmetic {D H δ ε : ℝ} (hD : 0 < D) (hH : 0 < H)
    (hδ : δ = 1 / (10 * D * H)) (hε : 0 ≤ ε) (hεu : ε ≤ δ / 4) :
    3 / δ + D * H - 4 / (δ + ε) < 0 := by
  have hd : 0 < δ := by rw [hδ]; positivity
  have hde : 0 < δ + ε := by linarith
  have hinv : 16 / (5 * δ) ≤ 4 / (δ + ε) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 5 * δ) hde).mpr
    nlinarith
  have heq : 3 / δ + D * H - 16 / (5 * δ) = -(D * H) := by
    rw [hδ]
    field_simp [hD.ne', hH.ne']
    ring
  have hle : 3 / δ + D * H - 4 / (δ + ε) ≤ 3 / δ + D * H - 16 / (5 * δ) := by
    linarith
  rw [heq] at hle
  exact hle.trans_lt (neg_neg_of_pos (mul_pos hD hH))

/-- A uniform logarithmic zero-free strip at sufficiently large height.
All constants are independent of the choice of nonprincipal character. -/
theorem modFive_nonprincipal_high_zero_free : ∃ c : ℝ, 0 < c ∧ ∃ T : ℝ, 2 < T ∧
    ∀ (χ : DirichletCharacter ℂ 5), χ ≠ 1 → ∀ (t β : ℝ), T ≤ |t| →
      1 - c / Real.log (|t| + 2) ≤ β →
      DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
  obtain ⟨C, hC, hchar⟩ := modFive_logderiv_growth_constant
  obtain ⟨S, hS, hsquare⟩ := modFive_square_logderiv_bound
  obtain ⟨δ0, hδ0, Z, hZ, hzeta⟩ := Erdos970.uniform_bound_Z0
  let D := 3 * Z + 4 * C + S + 1
  have hD1 : 1 ≤ D := by dsimp [D]; linarith
  have hD : 0 < D := zero_lt_one.trans_le hD1
  let b := 1 / (10 * D)
  have hb : 0 < b := by dsimp [b]; positivity
  have hbsmall : b ≤ 1 / 10 := by
    dsimp [b]
    apply (div_le_iff₀ (by positivity : 0 < 10 * D)).mpr
    linarith
  let T := Real.exp (1 + b / δ0) + 3
  have hT : 2 < T := by dsimp [T]; linarith [Real.exp_pos (1 + b / δ0)]
  refine ⟨b / 4, by positivity, T, hT, ?_⟩
  intro χ hχ t β ht hβ hzero
  have ht2 : 2 < |t| := hT.trans_le ht
  let H := Real.log (|t| + 2)
  have hHlarge : 1 + b / δ0 < H := by
    apply (Real.lt_log_iff_exp_lt (by positivity : 0 < |t| + 2)).mpr
    dsimp [T] at ht
    linarith
  have hH1 : 1 < H := by have := div_pos hb hδ0; linarith
  have hH : 0 < H := zero_lt_one.trans hH1
  let δ := b / H
  have hd : 0 < δ := div_pos hb hH
  have hdsmall : δ ≤ b := by
    apply (div_le_iff₀ hH).mpr
    nlinarith
  have hd1 : δ < 1 := by linarith
  have hd0 : δ < δ0 := by
    apply (div_lt_iff₀ hH).mpr
    have hm := (div_lt_iff₀ hδ0).mp (show b / δ0 < H by linarith)
    simpa only [mul_comm] using hm
  have hβ1 : β < 1 := by
    by_contra! h
    exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by simpa using h) hzero
  let ε := 1 - β
  have hε : 0 ≤ ε := by dsimp [ε]; linarith
  have hεu : ε ≤ δ / 4 := by
    dsimp [ε, δ, H] at *
    have he : (b / 4) / Real.log (|t| + 2) = (b / Real.log (|t| + 2)) / 4 := by ring
    rw [he] at hβ
    linarith
  have hβlow : 3 / 4 ≤ β := by dsimp [ε] at hεu; linarith
  have hc := (hchar χ hχ t (1 + δ) (by linarith) (by linarith)).2 β hβlow hβ1.le hzero
  have hs := hsquare χ t δ ht2 hd hd1
  have hz := hzeta δ hd hd0
  have hp := modFive_logderiv_positivity χ (σ := 1 + δ) (by linarith) t
  have hpoint : ((1 + δ : ℝ) : ℂ) = (1 : ℂ) + (δ : ℂ) := by push_cast; rfl
  simp only [Erdos970.logDerivZeta, ← neg_div] at hz
  rw [← hpoint] at hz
  have hdist : 1 + δ - β = δ + ε := by dsimp [ε]; ring
  rw [hdist] at hc
  have hcost : 3 * Z + (4 * C + S) * H ≤ D * H := by
    dsimp [D]
    nlinarith [mul_nonneg hZ (show 0 ≤ H - 1 by linarith)]
  have hpos : 0 ≤ 3 / δ + D * H - 4 / (δ + ε) := by
    have hm := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hz (by norm_num : (0 : ℝ) ≤ 3))
        (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 4))) hs
    have hexp : 3 * (1 / δ + Z) +
        4 * (C * Real.log (|t| + 2) - 1 / (δ + ε)) + S * Real.log (|t| + 2) =
        3 / δ + (3 * Z + (4 * C + S) * H) - 4 / (δ + ε) := by
      dsimp [H]
      ring
    rw [hexp] at hm
    have hh := hp.trans hm
    linarith only [hh, hcost]
  have hδeq : δ = 1 / (10 * D * H) := by
    change (1 / (10 * D)) / H = 1 / (10 * D * H)
    field_simp
  exact (not_lt_of_ge hpos) (modFive_zero_free_arithmetic hD hH hδeq hε hεu)

end TwoPointCorrelations

end OAI
