import OAI.NumberTheory.Ostmann.Arithmetic.MovingInternalErrorRate
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternSignedSum
import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkScale

namespace OAI

/-! # The original arithmetic error after summing all equality patterns -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem movingInternalArithmeticError_nonneg (n c d : ℕ) (F U α β V : ℝ)
    (hF : 1 ≤ F) (hU : 1 ≤ U) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 ≤ V) :
    0 ≤ movingInternalArithmeticError n c d F U α β V := by
  have hbase : 1 ≤ 2 * (F * U ^ d) := by
    have hh := one_le_mul_of_one_le_of_one_le hF (one_le_pow₀ hU (n := d))
    linarith
  have hh := one_le_pow₀ (one_le_pow₀ hbase (n := n + 1)) (n := 2)
  have hlog : 0 ≤ Real.log (2 * ((2 * (F * U ^ d)) ^ (n + 1)) ^ 2) :=
    Real.log_nonneg (by linarith)
  unfold movingInternalArithmeticError
  positivity

theorem movingInternalArithmeticError_card (n c d : ℕ) (F U α β V : ℝ) :
    movingInternalArithmeticError n c d F U α β V =
      c * movingInternalArithmeticError n 1 d F U α β V := by
  simp only [movingInternalArithmeticError, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

theorem movingInternalArithmeticError_mono_card (n c c' d : ℕ) (F U α β V : ℝ)
    (hcc : c ≤ c') (hF : 1 ≤ F) (hU : 1 ≤ U) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 ≤ V) :
    movingInternalArithmeticError n c d F U α β V ≤
      movingInternalArithmeticError n c' d F U α β V := by
  rw [movingInternalArithmeticError_card n c, movingInternalArithmeticError_card n c']
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcc)
    (movingInternalArithmeticError_nonneg n 1 d F U α β V hF hU hα hβ hV)

/-- A fixed-depth pattern sum retains any prescribed ordinary exponential
saving in the bulk count, and all arithmetic comparison errors stay negligible.
The antecedent is the explicit per-pattern bound proved for the original
harmonic prime laws, not a new analytic input. -/
theorem moving_arithmetic_pattern_sum_rate (n k : ℕ) (hk : 0 < k)
    (C D E Cprior B G : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hCprior : 1 ≤ Cprior) (hB : 0 ≤ B) :
    let J := 4 * n * 2 ^ n
    let gain := G + 2 * ((J ^ 2 + J : ℕ) : ℝ) * Cprior
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
      ∀ (d : ℕ) (F U α β Eprior cost : ℝ)
        (R : Setoid (Bool × MovingSampleIndex n) → ℂ),
        1 ≤ F → 1 ≤ U → 0 ≤ α →
        α ≤ Real.exp (E * L - Real.exp ((39 / 10000 : ℝ) * L)) → 0 ≤ β →
        Real.log F ≤ C * L → (d : ℝ) ≤ D * L →
        Real.log U ≤ Real.exp ((12 / 1000 : ℝ) * L) →
        β ≤ Real.exp (E * L - Real.exp ((1 / 100 : ℝ) * L)) →
        0 ≤ Eprior → Eprior ≤ Real.exp (Cprior * L) →
        0 ≤ cost → cost ≤ Real.exp (B * L ^ 2 + B * L * Real.exp ((1 / 1000 : ℝ) * L)) →
        (∀ s, ‖R s‖ ≤
          ((2 : ℝ) ^ Fintype.card (Quotient s) * Eprior ^ (J - Fintype.card (Quotient s))) *
            (cost * movingInternalArithmeticError n (Fintype.card (Quotient s)) d F U α β
              (Real.exp ((1 / 100 : ℝ) * L)) +
              (Real.exp (-gain * m) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
                2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))))) →
        ‖∑ s, R s‖ ≤ Real.exp (-G * m) +
          4 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  intro J gain
  let H : ℝ := ((J ^ 2 + J : ℕ) : ℝ) * Cprior
  have hH : 0 ≤ H := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hrate := arithmetic_error_absorption 0 (125 / 100000) (12 / 10000) H 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [moving_internal_error_with_cost n J C D E Cprior B
      hC hD hE hCprior hB, hrate, eventually_ge_atTop (4 : ℝ)]
    with L hinternal hrate hL4
  have hL : 1 ≤ L := by linarith
  simp only [one_mul, neg_mul] at hrate
  dsimp only
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  intro d F U α β Eprior cost R hF hU hα0 hα hβ0 hfreq hdegree hvalue hβ
    hEprior hEpriorup hcost hcostup hR
  let m := spectatorBulkCount k L
  let err := movingInternalArithmeticError n J d F U α β (Real.exp ((1 / 100 : ℝ) * L))
  let small := Real.exp (-gain * m) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
    2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))
  have hsmall0 : 0 ≤ small := by dsimp only [small]; positivity
  let budget := (2 : ℝ) ^ (J ^ 2) * (max 2 (Real.exp (Cprior * L))) ^ J
  have herr : 0 ≤ err := movingInternalArithmeticError_nonneg n J d F U α β _
    hF hU hα0 hβ0 (Real.exp_nonneg _)
  have hsum : ‖∑ s, R s‖ ≤ budget * (cost * err + small) := by
    have hh := movingPattern_error_sum_le n (Real.exp (Cprior * L)) (cost * err + small)
      (Real.exp_nonneg _) (add_nonneg (mul_nonneg hcost herr) hsmall0) R ?_
    · exact hh.trans_eq (by dsimp only [budget, J]; ring)
    · intro s
      have hc := movingPattern_quotient_card_le n s
      have he := movingInternalArithmeticError_mono_card n _ J d F U α β (Real.exp ((1 / 100 : ℝ) * L))
        hc hF hU hα0 hβ0 (Real.exp_nonneg _)
      have hp : (2 : ℝ) ^ Fintype.card (Quotient s) * Eprior ^ (J - Fintype.card (Quotient s)) ≤
          (2 : ℝ) ^ Fintype.card (Quotient s) *
            (Real.exp (Cprior * L)) ^ (J - Fintype.card (Quotient s)) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hEprior hEpriorup _) (by positivity)
      apply (hR s).trans
      have hminor := add_le_add (mul_le_mul_of_nonneg_left he hcost) (le_refl small)
      exact (mul_le_mul_of_nonneg_left hminor (by positivity)).trans
        ((mul_le_mul_of_nonneg_right hp (add_nonneg (mul_nonneg hcost herr) hsmall0)).trans_eq
          (mul_comm _ _))
  have hbudget : budget ≤ Real.exp (H * L) :=
    movingPattern_total_cost_le_exp n Cprior L hCprior hL
  have hmL : L ≤ 2 * m := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.succ_le_iff.mpr hk)
    have hk4 : (1 : ℝ) ≤ (k : ℝ) ^ 4 := one_le_pow₀ hk1 (n := 4)
    have hh := mul_le_mul_of_nonneg_right hk4 (by linarith : 0 ≤ L)
    have hhalf := spectatorBulkCount_half k L (by nlinarith)
    dsimp only [m]
    nlinarith
  have hmain : budget * Real.exp (-gain * m) ≤ Real.exp (-G * m) := by
    apply (mul_le_mul_of_nonneg_right hbudget (Real.exp_nonneg _)).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hmL hH
    dsimp only [gain, H] at hh ⊢
    nlinarith
  have hbulk : budget * Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) ≤
      Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
    apply (mul_le_mul_of_nonneg_right hbudget (Real.exp_nonneg _)).trans
    apply le_trans _ hrate
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    apply Real.exp_le_exp.mpr
    simp only [pow_one, zero_mul, Real.exp_zero, mul_one]
    nlinarith
  have hsmaller : Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) ≤
      Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) := by
    apply Real.exp_le_exp.mpr
    have hh := Real.exp_le_exp.mpr (show (125 / 100000 : ℝ) * L ≤ (2 / 1000 : ℝ) * L by linarith)
    linarith
  have hmid : Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) ≤
      Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
    apply Real.exp_le_exp.mpr
    have hh := Real.exp_le_exp.mpr
      (show (12 / 10000 : ℝ) * L ≤ (125 / 100000 : ℝ) * L by linarith)
    linarith
  have hint : budget * cost * err ≤ Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
    apply le_trans _ ((hinternal d F U α β hF hU hα0 hα hβ0 hfreq hdegree hvalue hβ).trans (hsmaller.trans hmid))
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcostup (by positivity)) herr
  have hrest := mul_le_mul_of_nonneg_left hsmaller (show 0 ≤ budget by positivity)
  have hall : budget * (cost * err + small) ≤ Real.exp (-G * m) +
      4 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
    dsimp only [small]
    nlinarith
  exact hsum.trans hall

end Ostmann

end OAI
