import OAI.NumberTheory.Ostmann.Construction.FinalExponentialContradiction
import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkScale
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticErrorRates

namespace OAI

/-! # The final contradiction with the actual arithmetic error scale -/

namespace Ostmann
open Filter

theorem arithmetic_error_sum_eventually (k : ℕ) (hk : 0 < k) (T : ℝ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      Real.exp (-(T + 1) * m) + 4 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) ≤
        Real.exp (-T * m) := by
  let A := max T 0 * (k : ℝ) ^ 4
  let C := A + 4
  have hA : 0 ≤ A := mul_nonneg (le_max_right _ _) (by positivity)
  filter_upwards [arithmetic_exponent_absorption 0 (12 / 10000) 0 C 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    (spectatorBulkCount_tendsto k hk).eventually (eventually_ge_atTop (Real.log 2)),
    eventually_ge_atTop (1 : ℝ)] with L hrate hm hL
  dsimp only
  let m := spectatorBulkCount k L
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have htm : T * m ≤ A * L := by
    apply (mul_le_mul_of_nonneg_right (le_max_left _ _) hm0).trans
    exact (mul_le_mul_of_nonneg_left (spectatorBulkCount_upper k L (by linarith))
      (le_max_right _ _)).trans_eq (by dsimp only [A]; ring)
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog4 : Real.log 4 ≤ 3 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hs : T * m + Real.log 4 + Real.log 2 ≤ Real.exp ((12 / 10000 : ℝ) * L) := by
    simp only [pow_one, zero_mul, Real.exp_zero, mul_one, one_mul] at hrate
    have haL : 0 ≤ A * L := mul_nonneg hA (by linarith)
    have hAL : A ≤ A * L := le_mul_of_one_le_right hA hL
    dsimp only [C] at hrate
    nlinarith
  have hfirst : Real.exp (-(T + 1) * m) ≤ Real.exp (-T * m - Real.log 2) := by
    apply Real.exp_le_exp.mpr
    change Real.log 2 ≤ (m : ℝ) at hm
    nlinarith
  have hsecond : 4 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) ≤
      Real.exp (-T * m - Real.log 2) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4), ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ Real.exp (-T * m - Real.log 2) + Real.exp (-T * m - Real.log 2) :=
      add_le_add hfirst hsecond
    _ = _ := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring

/-- The final comparison needs precisely the ordinary exponential bulk
saving supplied by the quartet argument, plus the negligible arithmetic
error. No double-exponential assumption is made on that bulk saving. -/
theorem eventual_final_arithmetic_contradiction (n k : ℕ) (hk : 0 < k)
    (B₁ D C δ : ℝ) (hδ : 0 < δ)
    (hentropy : C + D + 2 * B₁ + δ ≤ (n : ℝ) * Real.log 2 - 1) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (T B E : ℝ) (η : ℂ),
      T ≤ Real.exp (D * (2 ^ (n + 1) : ℝ) * m) → 0 ≤ B → 0 ≤ E →
      B ≤ Real.exp (C * (2 ^ (n + 1) : ℝ) * m) →
      E ≤ Real.exp (-((D + 2 * B₁ + δ) * (2 ^ (n + 1) : ℝ) + 1) * m) +
        4 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) →
      Real.exp (-B₁ * (2 ^ (n + 1) : ℝ) * m) ≤ ‖η‖ →
      ‖η‖ ^ 2 ≤ T * (B / (Fintype.card (FinalParityReassignments n m) : ℝ) + E) → False := by
  have hpos : 0 < δ * (2 ^ (n + 1) : ℝ) := by positivity
  filter_upwards [arithmetic_error_sum_eventually k hk
      ((D + 2 * B₁ + δ) * (2 ^ (n + 1) : ℝ)),
    (spectatorBulkCount_tendsto k hk).eventually
      (eventually_gt_atTop (Real.log 2 / (δ * (2 ^ (n + 1) : ℝ))))] with L herror hmargin
  dsimp only
  intro T B E η hT hB0 hE0 hB hE hlower hcompare
  have hE' : E ≤ Real.exp (-(D + 2 * B₁ + δ) * (2 ^ (n + 1) : ℝ) * spectatorBulkCount k L) := by
    exact (hE.trans herror).trans_eq (by congr 1; ring)
  have hm : Real.log 2 < δ * (2 ^ (n + 1) : ℝ) * spectatorBulkCount k L := by
    have hh := (div_lt_iff₀ hpos).mp hmargin
    nlinarith
  exact final_exponential_contradiction n (spectatorBulkCount k L) B₁ D C δ T B E η
    hT hB0 hE0 hB hE' hentropy hm hlower hcompare

end Ostmann

end OAI
