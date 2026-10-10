import OAI.NumberTheory.Ostmann.Preliminaries.MertensPrimeBands

namespace OAI

/-! # Mertens' second theorem on the iterated-logarithm band

F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, J. reine angew.
Math. 78 (1874), 46–62, second theorem. We only require its weaker bounded
error consequence `sum_{p≤Q} 1/p = log log Q + O(1)`. The pinned PNT library
states this specialization as `Mertens.sum_prime_div_eq_log_log`.
-/

namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- Precise published Mertens-second input, weaker than its convergent-error
form and sufficient for the favorable-prime harmonic mass. -/
def MertensHarmonicEstimate (C : ℝ) : Prop :=
  ∀ Q : ℕ, 2 ≤ Q → |(∑ p ∈ Nat.primesLE Q, (p : ℝ)⁻¹) - Real.log (Real.log Q)| ≤ C

noncomputable def logLogPrimeBand (L : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊Real.exp (Real.exp ((9 / 10 : ℝ) * L))⌋₊ \
    Nat.primesLE ⌊Real.exp (Real.exp ((1 / 20 : ℝ) * L))⌋₊

private theorem floor_exp_loglog_bounds (s : ℝ) (hs : 2 ≤ s) :
    2 ≤ ⌊Real.exp (Real.exp s)⌋₊ ∧
      s - Real.log 2 ≤ Real.log (Real.log (⌊Real.exp (Real.exp s)⌋₊ : ℝ)) ∧
      Real.log (Real.log (⌊Real.exp (Real.exp s)⌋₊ : ℝ)) ≤ s := by
  have he : 2 ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
  have hf := floor_exp_log_bounds (Real.exp s) (by linarith)
  have hQ : 2 ≤ ⌊Real.exp (Real.exp s)⌋₊ := by
    apply Nat.le_floor
    norm_num only [Nat.cast_ofNat]
    linarith [Real.add_one_le_exp (Real.exp s)]
  have hlogQ : 0 < Real.log (⌊Real.exp (Real.exp s)⌋₊ : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < ⌊Real.exp (Real.exp s)⌋₊ by omega))
  have h2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hh : Real.exp s / 2 ≤ Real.log (⌊Real.exp (Real.exp s)⌋₊ : ℝ) := by
    linarith [hf.2.1]
  refine ⟨hQ, ?_, ?_⟩
  · have hl := Real.log_le_log (show 0 < Real.exp s / 2 by positivity) hh
    rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at hl
    exact hl
  · have hu := Real.log_le_log hlogQ hf.2.2
    simpa only [Real.log_exp] using hu

theorem logLogPrimeBand_mem {L : ℝ} {p : ℕ} (hp : p ∈ logLogPrimeBand L) :
    p.Prime ∧ Real.exp ((1 / 20 : ℝ) * L) < Real.log (p : ℝ) ∧
      Real.log (p : ℝ) ≤ Real.exp ((9 / 10 : ℝ) * L) := by
  obtain ⟨hhi, hlo⟩ := Finset.mem_sdiff.mp hp
  have hprime := Nat.prime_of_mem_primesLE hhi
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hlo' : ⌊Real.exp (Real.exp ((1 / 20 : ℝ) * L))⌋₊ < p := by
    by_contra hn
    exact hlo (Nat.mem_primesLE.mpr ⟨Nat.le_of_not_gt hn, hprime⟩)
  have hloR : Real.exp (Real.exp ((1 / 20 : ℝ) * L)) < (p : ℝ) :=
    (Nat.floor_lt (Real.exp_nonneg _)).mp hlo'
  have hhiR : (p : ℝ) ≤ Real.exp (Real.exp ((9 / 10 : ℝ) * L)) :=
    (Nat.cast_le.mpr (Nat.le_of_mem_primesLE hhi)).trans (Nat.floor_le (Real.exp_nonneg _))
  exact ⟨hprime, (Real.lt_log_iff_exp_lt hp0).mpr hloR,
    (Real.log_le_iff_le_exp hp0).mpr hhiR⟩

theorem logLogPrimeBand_harmonic_lower {C : ℝ} (hM : MertensHarmonicEstimate C)
    (L : ℝ) (hL : 40 ≤ L) :
    (17 / 20 : ℝ) * L - Real.log 2 - 2 * C ≤
      ∑ p ∈ logLogPrimeBand L, (p : ℝ)⁻¹ := by
  have hlo := floor_exp_loglog_bounds ((1 / 20 : ℝ) * L) (by linarith)
  have hhi := floor_exp_loglog_bounds ((9 / 10 : ℝ) * L) (by linarith)
  have hsub : Nat.primesLE ⌊Real.exp (Real.exp ((1 / 20 : ℝ) * L))⌋₊ ⊆
      Nat.primesLE ⌊Real.exp (Real.exp ((9 / 10 : ℝ) * L))⌋₊ := by
    intro p hp
    refine Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE hp).trans ?_, Nat.prime_of_mem_primesLE hp⟩
    apply Nat.floor_mono
    apply Real.exp_le_exp.mpr
    apply Real.exp_le_exp.mpr
    linarith
  rw [logLogPrimeBand, Finset.sum_sdiff_eq_sub hsub]
  have hlow := (abs_le.mp (hM _ hhi.1)).1
  have hupp := (abs_le.mp (hM _ hlo.1)).2
  linarith [hhi.2.1, hlo.2.2]

theorem logLogPrimeBand_harmonic_upper {C : ℝ} (hM : MertensHarmonicEstimate C)
    (L : ℝ) (hL : 40 ≤ L) :
    (∑ p ∈ logLogPrimeBand L, (p : ℝ)⁻¹) ≤
      (17 / 20 : ℝ) * L + Real.log 2 + 2 * C := by
  have hlo := floor_exp_loglog_bounds ((1 / 20 : ℝ) * L) (by linarith)
  have hhi := floor_exp_loglog_bounds ((9 / 10 : ℝ) * L) (by linarith)
  have hsub : Nat.primesLE ⌊Real.exp (Real.exp ((1 / 20 : ℝ) * L))⌋₊ ⊆
      Nat.primesLE ⌊Real.exp (Real.exp ((9 / 10 : ℝ) * L))⌋₊ := by
    intro p hp
    refine Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE hp).trans ?_, Nat.prime_of_mem_primesLE hp⟩
    apply Nat.floor_mono
    apply Real.exp_le_exp.mpr
    apply Real.exp_le_exp.mpr
    linarith
  rw [logLogPrimeBand, Finset.sum_sdiff_eq_sub hsub]
  have hlow := (abs_le.mp (hM _ hlo.1)).1
  have hupp := (abs_le.mp (hM _ hhi.1)).2
  linarith [hlo.2.1, hhi.2.2]

theorem eventual_logLogPrimeBand_harmonic_le {C : ℝ} (hM : MertensHarmonicEstimate C) :
    ∀ᶠ L : ℝ in Filter.atTop, (∑ p ∈ logLogPrimeBand L, (p : ℝ)⁻¹) ≤ L := by
  filter_upwards [Filter.eventually_ge_atTop (max 40 ((20 / 3 : ℝ) * (Real.log 2 + 2 * C)))]
    with L hL
  have hh := logLogPrimeBand_harmonic_upper hM L ((le_max_left _ _).trans hL)
  have hnum := (le_max_right 40 ((20 / 3 : ℝ) * (Real.log 2 + 2 * C))).trans hL
  linarith

end Ostmann

end OAI
