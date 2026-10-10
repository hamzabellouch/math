import OAI.Analysis.LipschitzHilbert.Estimates.SequenceExponents
import Mathlib.Analysis.MeanInequalitiesPow

namespace OAI

/-! Monotonicity of finite sequence norms and the small-remainder estimate. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

theorem sum_rpow_le_rpow_sum (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    {p : ℝ} (hp : 1 ≤ p) : (∑ i, x i ^ p) ≤ (∑ i, x i) ^ p := by
  have hp0 : 0 < p := by linarith
  have h (s : Finset ι) : (∑ i ∈ s, x i ^ p) ≤ (∑ i ∈ s, x i) ^ p := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [Real.zero_rpow hp0.ne']
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      calc
        x i ^ p + ∑ j ∈ s, x j ^ p ≤ x i ^ p + (∑ j ∈ s, x j) ^ p :=
          add_le_add le_rfl ih
        _ ≤ (x i + ∑ j ∈ s, x j) ^ p :=
          Real.add_rpow_le_rpow_add (hx i) (Finset.sum_nonneg (fun j _ => hx j)) hp
  exact h Finset.univ

theorem sum_powers_exponent_comparison (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (∑ i, x i ^ q) ≤ (∑ i, x i ^ p) ^ (q / p) := by
  have h := sum_rpow_le_rpow_sum (fun i => x i ^ p)
    (fun i => Real.rpow_nonneg (hx i) p) ((le_div_iff₀ hp).2 (by simpa using hpq))
  have heq (i : ι) : (x i ^ p) ^ (q / p) = x i ^ q := by
    rw [← Real.rpow_mul (hx i)]
    congr 1
    field_simp
  simpa only [heq] using h

/-- A sequence norm is written as a real power of its finite power sum. -/
def sequenceNorm (a : ι → ℂ) (r : ℝ) : ℝ := (∑ i, ‖a i‖ ^ r) ^ (1 / r)

theorem sequenceNorm_nonneg (a : ι → ℂ) (r : ℝ) : 0 ≤ sequenceNorm a r :=
  Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg (a i)) _)) _

theorem sequenceNorm_rpow (a : ι → ℂ) (r q : ℝ) :
    sequenceNorm a r ^ q = (∑ i, ‖a i‖ ^ r) ^ (q / r) := by
  unfold sequenceNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg
    (fun i _ => Real.rpow_nonneg (norm_nonneg _) _))]
  congr 1
  ring

theorem sequenceNorm_mono (a : ι → ℂ) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    sequenceNorm a q ≤ sequenceNorm a p := by
  have hq : 0 < q := hp.trans_le hpq
  have h := Real.rpow_le_rpow (Finset.sum_nonneg
    (fun i _ => Real.rpow_nonneg (norm_nonneg (a i)) q))
    (sum_powers_exponent_comparison (fun i => ‖a i‖) (fun i => norm_nonneg _) hp hpq)
    (show 0 ≤ 1 / q by positivity)
  rw [← Real.rpow_mul (Finset.sum_nonneg
    (fun i _ => Real.rpow_nonneg (norm_nonneg (a i)) p))] at h
  have heq : q / p * (1 / q) = 1 / p := by field_simp
  simpa only [heq, sequenceNorm] using h

theorem sum_squares_le_sequenceNorm_sq (a : ι → ℂ) {r : ℝ}
    (hr : 0 < r) (hr2 : r ≤ 2) :
    (∑ i, ‖a i‖ ^ 2) ≤ sequenceNorm a r ^ 2 := by
  have h := sum_powers_exponent_comparison (fun i => ‖a i‖)
    (fun i => norm_nonneg _) hr hr2
  simpa only [Real.rpow_ofNat, ← sequenceNorm_rpow a r 2] using h

theorem sequenceNorm_fourth_le_mass_cube (a : ι → ℂ) {r : ℝ} (hr : 4 / 3 ≤ r) :
    sequenceNorm a r ^ 4 ≤ (∑ i, coefficientMass a i) ^ 3 := by
  have h := pow_le_pow_left₀ (sequenceNorm_nonneg a r)
    (sequenceNorm_mono a (by norm_num : (0 : ℝ) < 4 / 3) hr) 4
  have heq : sequenceNorm a (4 / 3) ^ (4 : ℕ) = (∑ i, coefficientMass a i) ^ 3 := by
    rw [← Real.rpow_natCast, sequenceNorm_rpow]
    norm_num [coefficientMass]
  rwa [heq] at h

/-- The exact numerical smallness needed for the dominant coefficient case. -/
theorem sequenceNorm_le_one_div_sixtyfour (a : ι → ℂ) {r : ℝ}
    (hr : 4 / 3 ≤ r) (hsmall : ∑ i, coefficientMass a i ≤ 1 / 1023) :
    sequenceNorm a r ≤ 1 / 64 := by
  have hcube : (∑ i, coefficientMass a i) ^ 3 ≤ (1 / 1023 : ℝ) ^ 3 :=
    pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ => coefficientMass_nonneg a i)) hsmall 3
  have hfourth : sequenceNorm a r ^ 4 ≤ (1 / 64 : ℝ) ^ 4 :=
    (sequenceNorm_fourth_le_mass_cube a hr).trans (hcube.trans (by norm_num))
  exact (pow_le_pow_iff_left₀ (sequenceNorm_nonneg a r) (by norm_num : (0 : ℝ) ≤ 1 / 64)
    (by decide : (4 : ℕ) ≠ 0)).mp hfourth

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
