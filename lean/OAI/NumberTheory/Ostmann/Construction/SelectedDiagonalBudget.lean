import OAI.NumberTheory.Ostmann.Construction.SelectedBadDiagonalRate
import OAI.NumberTheory.Ostmann.Arithmetic.MovingHarmonicScale
import OAI.NumberTheory.Ostmann.Arithmetic.MovingDiagonalErrorBudget

namespace OAI

/-! # All terms of the selected logarithmic diagonal fit the iteration reserve -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem selected_diagonal_budget {CM : ℝ} (hM : MertensEstimate CM)
    (n s k : ℕ) (hk : 0 < k) (c K Bs BD Bz B ε εdiag : ℝ)
    (hc : 0 < c) (hK : 0 ≤ K) (hBs : 0 ≤ Bs) (hBD0 : 0 ≤ BD)
    (hε : 0 < ε) (hεdiag : 0 ≤ εdiag)
    (hbudget : 4 * (K + 1) * s ≤ ε * (k : ℝ) ^ 4) (hBz : 9 ≤ Bz)
    (hBD : Bs + 2 * B +
      (Real.log 2 - Real.log (1 / 16000 : ℝ) + 5 / 4 + ε + Real.log 12 + 1 + εdiag) + 6 ≤ BD) :
    let r : ℝ := (2 ^ n : ℕ)
    let gain := max 0 ((Real.log 2 + Real.log ((k : ℝ) ^ 4 / (1 / 16000 : ℝ)) +
      Real.log r + ε + 2 * B + 6) * r)
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      let z := (k : ℝ) ^ 4
      let Δ := spectatorBaseGap Bs z m
      let bad := (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
        Real.exp (r * m * (-(3 / 4 : ℝ) * Real.log r + 5 / 4))
      ∀ (global : Finset ℕ) (Q : MovingRegularSlot n s m → Finset ℕ),
      (global.card : ℝ) ≤ Real.exp ((K + 1) * L) →
      (∀ j, Q (movingTemplateBulk n s m j) =
        primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
          (Real.exp ((6 / 1000 : ℝ) * L)) \ global) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Q j, (q : ℝ)⁻¹) →
      ∀ arch : ℝ, 0 ≤ arch → arch ≤ Real.exp (-spectatorStepGap BD Bz z r m) →
      arch * (((Fintype.card (MovingRegularSlot n s m)).factorial : ℝ) *
        (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹)) *
        (4 * (bad * (Real.exp (r * Δ + (Real.log 12 + 1) * r * m + εdiag * m) +
          5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) +
          Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)))) ≤
          Real.exp (-(2 * B + 3) * r * m) := by
  intro r gain
  have hr : 1 ≤ r := by dsimp [r]; exact_mod_cast Nat.one_le_two_pow
  have hz : 1 ≤ (k : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast hk)
  have hg0 : 0 ≤ gain := le_max_left _ _
  filter_upwards [selected_bad_diagonal_rate hM n s k hk c K Bs BD Bz B ε εdiag
      hc hK hε hεdiag hbudget hBz hBD,
    eventual_moving_harmonic_scale n s k hk (K + 1) (1 / 16000) ε (by norm_num) hε hbudget,
    whole_shell_retained_linear_mass hM (K + 1) (by linarith),
    eventual_moving_comparison_error k gain hg0,
    (spectatorBulkCount_tendsto k hk).eventually (eventually_ge_atTop (Real.log 48)),
    eventually_ge_atTop (max 1 (-Real.log c))] with L hbad hnorm hbulk herr hm hL
  dsimp only at hbad hnorm ⊢
  intro global Q hglobal hQ hmass arch harch0 harch
  let m := spectatorBulkCount k L
  let Z : ℝ := ((Fintype.card (MovingRegularSlot n s m)).factorial : ℝ) *
    (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹)
  let D := Real.exp (r * spectatorBaseGap Bs ((k : ℝ) ^ 4) m +
    (Real.log 12 + 1) * r * m + εdiag * m)
  let bad := (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
    Real.exp (r * m * (-(3 / 4 : ℝ) * Real.log r + 5 / 4))
  let E := Real.exp (-(2 * B + 6) * r * m)
  have hZ0 : 0 ≤ Z := by dsimp [Z]; positivity
  have hb : (arch * Z) * bad * D ≤ E := by
    have h := hbad global Q hglobal hQ hmass arch harch
    change arch * (bad * Z) * D ≤ E at h
    convert h using 1; ring
  have hmassBound := hnorm (fun i => ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (fun j => selected_prime_mass_exp_lower c K L hc hL _ (hmass _))
    (fun j => by rw [show (j.1, Sum.inr j.2) = movingTemplateBulk n s m j from rfl, hQ j]
                 convert hbulk global hglobal using 1; ring)
  let A := Real.log 2 + Real.log ((k : ℝ) ^ 4 / (1 / 16000 : ℝ)) + Real.log r + ε
  have hZ : Z ≤ Real.exp (A * r * m) := by
    simpa only [Z, A, r, m, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using hmassBound
  have hstep : 0 ≤ spectatorStepGap BD Bz ((k : ℝ) ^ 4) r m := by
    unfold spectatorStepGap
    have hzlog := Real.log_nonneg hz
    have hrlog := Real.log_nonneg hr
    have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
    positivity
  have harch1 : arch ≤ 1 := harch.trans ((Real.exp_le_one_iff.mpr (by linarith :
    -spectatorStepGap BD Bz ((k : ℝ) ^ 4) r m ≤ 0)))
  have hg : (arch * Z) * Real.exp (-gain * m) ≤ E := by
    apply (mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_right harch1 hZ0).trans (by simpa using hZ)) (Real.exp_nonneg _)).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hgg : (A + 2 * B + 6) * r ≤ gain := le_max_right _ _
    have hgm := mul_le_mul_of_nonneg_right hgg (Nat.cast_nonneg m (α := ℝ))
    linarith
  have hD : 1 ≤ D := by
    apply Real.one_le_exp
    have hzlog := Real.log_nonneg hz
    have h12 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 12)
    dsimp only [D, spectatorBaseGap]
    positivity
  have heD : Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) ≤ D :=
    (Real.exp_le_one_iff.mpr (by linarith [Real.exp_pos ((12 / 10000 : ℝ) * L)])).trans hD
  apply moving_diagonal_reserve B r m _ (by
    have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
    have hlog : 0 ≤ Real.log 48 := Real.log_nonneg (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right hr hm0])
  exact moving_diagonal_four_term_bound (arch * Z) bad D (Real.exp (-gain * m))
    (Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) E
    (mul_nonneg harch0 hZ0) (by dsimp [bad]; positivity) heD herr hb hg

end Ostmann

end OAI
