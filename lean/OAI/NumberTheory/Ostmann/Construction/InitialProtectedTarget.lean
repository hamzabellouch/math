import OAI.NumberTheory.Ostmann.Construction.RoundedProtectedTarget
import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkScale

namespace OAI

/-! # The actual two cutoff centers fit the protected target -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def movingInitialGapTotal (k : ℕ) (Bs BD Bz L : ℝ) : ℝ :=
  spectatorBaseGap Bs ((k : ℝ) ^ 4) (spectatorBulkCount k L) +
    ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4)
      ((2 : ℝ) ^ (i : ℕ)) (spectatorBulkCount k L)

theorem movingInitialGapTotal_linear (k : ℕ) (Bs BD Bz L : ℝ) :
    movingInitialGapTotal k Bs BD Bz L =
      (spectatorBaseGap Bs ((k : ℝ) ^ 4) 1 +
        ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4) ((2 : ℝ) ^ (i : ℕ)) 1) *
          spectatorBulkCount k L := by
  simp only [movingInitialGapTotal, spectatorBaseGap, spectatorStepGap, mul_one,
    add_mul, Finset.sum_mul]

theorem initial_log_center_bounds (m : ℕ) (T : ℝ) (c : ℤ)
    (hc : c ∈ Finset.Icc (0 : ℤ) ⌈(m / 2 : ℕ) * Real.exp T⌉₊) :
    0 ≤ (c : ℝ) ∧ (c : ℝ) ≤ (m : ℝ) * Real.exp T + 1 := by
  have hc0 : 0 ≤ (c : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hc).1
  have hcu : (c : ℝ) ≤ (⌈(m / 2 : ℕ) * Real.exp T⌉₊ : ℕ) := by
    exact_mod_cast (Finset.mem_Icc.mp hc).2
  have hn : ((m / 2 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.div_le_self m 2
  have he := Nat.ceil_lt_add_one (show 0 ≤ ((m / 2 : ℕ) : ℝ) * Real.exp T by positivity)
  exact ⟨hc0, hcu.trans (he.le.trans (by gcongr))⟩

theorem eventual_initial_protected_target (k : ℕ) (hk : 2 ≤ k)
    (Bs BD Bz : ℝ) (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) :
    ∀ᶠ L : ℝ in atTop, ∀ cb cd : ℤ,
      cb ∈ Finset.Icc (0 : ℤ)
        ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 1000 : ℝ) * L)⌉₊ →
      cd ∈ Finset.Icc (0 : ℤ)
        ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 10000 : ℝ) * L)⌉₊ →
      ∀ lo G Y : ℝ,
      2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y →
      Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) + 1 →
      lo - 2 ≤ G → G ≤ lo - 2 + 12 * Real.exp ((1 / 100 : ℝ) * L) →
      let J := movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L)
      16 * Real.exp ((1 / 100 : ℝ) * L) ≤ J ∧
      J ≤ 32 * Real.exp ((1 / 100 : ℝ) * L) ∧
      0 ≤ 2 * (cb : ℝ) ∧ 2 * (cb : ℝ) ≤ J / 4 := by
  let z : ℝ := (k : ℝ) ^ 4
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hz1 : 1 ≤ z := one_le_pow₀ (by exact_mod_cast (show 1 ≤ k by omega))
  have hlogz : 0 ≤ Real.log z := Real.log_nonneg hz1
  let R := spectatorBaseGap Bs z 1 +
    ∑ i : Fin k, spectatorStepGap BD Bz z ((2 : ℝ) ^ (i : ℕ)) 1
  have hR : 0 ≤ R := by
    dsimp only [R, spectatorBaseGap]
    apply add_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro i _
    have hl : 0 ≤ Real.log ((2 : ℝ) ^ (i : ℕ)) :=
      Real.log_nonneg (one_le_pow₀ (by norm_num))
    dsimp only [spectatorStepGap]
    positivity
  let C := max (R * z) (z + 1)
  have hC : 0 ≤ C := (by linarith only [hz] : 0 ≤ z + 1).trans (le_max_right _ _)
  filter_upwards [eventual_protected_target_error C,
    arithmetic_exponent_absorption (6 / 1000) (1 / 100) 0 (z + 1) 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L herror hsmall hL
  intro cb cd hcb hcd lo G Y hYlo hYhi hGlo hGhi J
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hm : (spectatorBulkCount k L : ℝ) ≤ z * L := spectatorBulkCount_upper k L hL0
  obtain ⟨hcb0, hcbU⟩ := initial_log_center_bounds _ _ cb hcb
  obtain ⟨hcd0, hcdU⟩ := initial_log_center_bounds _ _ cd hcd
  have he : Real.exp ((6 / 10000 : ℝ) * L) ≤ Real.exp ((1 / 1000 : ℝ) * L) :=
    Real.exp_le_exp.mpr (by linarith only [hL0])
  have hE : 1 ≤ Real.exp ((1 / 1000 : ℝ) * L) := Real.one_le_exp (by positivity)
  have hcd1 : (cd : ℝ) ≤ z * L * Real.exp ((1 / 1000 : ℝ) * L) + 1 := by
    have hh := mul_le_mul hm he (Real.exp_nonneg _) (show 0 ≤ z * L by positivity)
    linarith only [hcdU, hh]
  have hcdC : (cd : ℝ) ≤ C * L * Real.exp ((1 / 1000 : ℝ) * L) := by
    have hc := mul_le_mul_of_nonneg_right (le_max_right (R * z) (z + 1))
      (mul_nonneg hL0 (Real.exp_nonneg ((1 / 1000 : ℝ) * L)))
    have hLE : 1 ≤ L * Real.exp ((1 / 1000 : ℝ) * L) := by nlinarith only [hL, hE]
    dsimp only [C]
    nlinarith only [hcd1, hc, hLE]
  have hgap0 : 0 ≤ movingInitialGapTotal k Bs BD Bz L := by
    rw [movingInitialGapTotal_linear]
    exact mul_nonneg hR (Nat.cast_nonneg _)
  have hgapU : movingInitialGapTotal k Bs BD Bz L ≤ C * L := by
    rw [movingInitialGapTotal_linear]
    have hh := mul_le_mul_of_nonneg_right (le_max_left (R * z) (z + 1)) hL0
    have hh' := mul_le_mul_of_nonneg_left hm hR
    change R * (spectatorBulkCount k L : ℝ) ≤ C * L
    dsimp only [C]
    nlinarith only [hh, hh']
  have herr := herror _ cd hgap0 hgapU hcd0 hcdC
  obtain ⟨hJlo, hJhi⟩ := movingProtectedTarget_rounded_bounds k hk _ lo G Y cd _
    (Real.one_le_exp (by positivity)) hYlo hYhi hGlo hGhi herr
  have hcb1 : (cb : ℝ) ≤ z * L * Real.exp ((6 / 1000 : ℝ) * L) + 1 := by
    have hh := mul_le_mul_of_nonneg_right hm (Real.exp_nonneg ((6 / 1000 : ℝ) * L))
    linarith only [hcbU, hh]
  simp only [pow_one, zero_mul, Real.exp_zero, one_mul] at hsmall
  have hmul : 0 ≤ (z + 1) * L := mul_nonneg (by positivity) hL0
  have hcb2 : (cb : ℝ) ≤ Real.exp ((1 / 100 : ℝ) * L) := by
    have hh : 0 ≤ L * Real.exp ((6 / 1000 : ℝ) * L) := by positivity
    nlinarith only [hcb1, hsmall, hmul, hh]
  exact ⟨hJlo, hJhi, by linarith only [hcb0], by
    dsimp only [J]
    linarith only [hJlo, hcb2, Real.exp_nonneg ((1 / 100 : ℝ) * L)]⟩

end Ostmann

end OAI
