import OAI.NumberTheory.TwoPointCorrelations.ModFiveUnsmoothingScale

namespace OAI

/-! Removal of the nonintegral-cutoff condition.  The Mangoldt sums only
depend on the floor; the midpoint of the same unit interval is always an
admissible triangular cutoff. -/

namespace TwoPointCorrelations

open Filter

lemma modFive_half_cutoff_nonnat (N : ℕ) :
    ∀ n : ℕ, (N : ℝ) + 1 / 2 ≠ (n : ℝ) := by
  intro n he
  have hh : (2 : ℝ) * (N : ℝ) + 1 = 2 * (n : ℝ) := by linarith
  have hn : 2 * N + 1 = 2 * n := by exact_mod_cast hh
  omega

lemma modFive_half_cutoff_floor (N : ℕ) :
    ⌊(N : ℝ) + 1 / 2⌋₊ = N := by
  apply (Nat.floor_eq_iff (by positivity)).mpr
  constructor <;> linarith

lemma modFive_half_cutoff_geometry {x : ℝ} (hx : 4 ≤ x) :
    x / 2 ≤ (⌊x⌋₊ : ℝ) + 1 / 2 ∧
    (⌊x⌋₊ : ℝ) + 1 / 2 ≤ 2 * x ∧
    Real.sqrt (Real.log x) / 2 ≤ Real.sqrt (Real.log ((⌊x⌋₊ : ℝ) + 1 / 2)) := by
  have hxp : 0 < x := by linarith
  have hfloor := Nat.floor_le hxp.le
  have hfloorlt := Nat.lt_floor_add_one x
  have htlow : x / 2 ≤ (⌊x⌋₊ : ℝ) + 1 / 2 := by linarith
  have hthi : (⌊x⌋₊ : ℝ) + 1 / 2 ≤ 2 * x := by linarith
  refine ⟨htlow, hthi, ?_⟩
  have htp : 0 < (⌊x⌋₊ : ℝ) + 1 / 2 := by positivity
  have hlogx : 2 * Real.log 2 ≤ Real.log x := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hx
    have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    linarith
  have hlogt : Real.log x - Real.log 2 ≤ Real.log ((⌊x⌋₊ : ℝ) + 1 / 2) := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < x / 2) htlow
    rwa [Real.log_div hxp.ne' (by norm_num)] at hh
  have hlogtnonneg : 0 ≤ Real.log ((⌊x⌋₊ : ℝ) + 1 / 2) :=
    Real.log_nonneg (by linarith)
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hlogtnonneg, div_pow, Real.sq_sqrt (Real.log_nonneg (by linarith))]
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  norm_num
  linarith

/-- The full real-cutoff estimate for every nonprincipal character mod 5. -/
theorem modFive_nonprincipal_psi_decay : ∃ c : ℝ, 0 < c ∧
    ∀ᶠ x : ℝ in atTop, ∀ χ : DirichletCharacter ℂ 5, χ ≠ 1 →
      ‖modFiveTwistedPsi χ x‖ ≤ 2 * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc, hbound⟩ := modFive_unsmoothed_decay_nonnat
  obtain ⟨X, hX⟩ := eventually_atTop.mp hbound
  refine ⟨c / 2, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max 4 (2 * X))] with x hx χ hχ
  have hx4 : 4 ≤ x := (le_max_left _ _).trans hx
  obtain ⟨htlow, hthi, hroot⟩ := modFive_half_cutoff_geometry hx4
  let t := (⌊x⌋₊ : ℝ) + 1 / 2
  have htX : X ≤ t := by
    have hlarge : 2 * X ≤ x := (le_max_right _ _).trans hx
    dsimp [t]
    linarith
  have ht : 0 < t := by dsimp [t]; positivity
  have hsum : modFiveTwistedPsi χ t = modFiveTwistedPsi χ x := by
    simp only [modFiveTwistedPsi, t, modFive_half_cutoff_floor]
  have hm := hX t htX χ hχ (modFive_half_cutoff_nonnat ⌊x⌋₊)
  rw [hsum] at hm
  have he : Real.exp (-c * Real.sqrt (Real.log t)) ≤
      Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonpos_left hroot (neg_nonpos.mpr hc.le)
    dsimp [t] at *
    nlinarith
  exact hm.trans (mul_le_mul hthi he (Real.exp_pos _).le (by linarith))

end TwoPointCorrelations

end OAI
