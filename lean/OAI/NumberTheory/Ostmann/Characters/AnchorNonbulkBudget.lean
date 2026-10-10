import OAI.NumberTheory.Ostmann.Arithmetic.NonbulkHarmonicBudget
import OAI.NumberTheory.Ostmann.Construction.CellRoleBudget
import OAI.NumberTheory.Ostmann.Construction.ActiveNonbulkCount

namespace OAI

/-! # Nonbulk normalization at the manuscript's exponential bulk scale -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_anchor_nonbulk_cost (n B : ℕ) (c ε z : ℝ)
    (_hc : 0 ≤ c) (hε : 0 < ε) (hz : 0 < z)
    (hbudget : 4 * c * B ≤ ε * z) :
    ∀ᶠ L : ℝ in atTop, ∀ (m : ℕ), z * L / 2 ≤ (m : ℝ) →
      nonbulkCombinatorialCost n B * Real.exp (c * L * (2 ^ n * B : ℕ)) ≤
        Real.exp (ε * (2 ^ n : ℕ) * (m : ℝ)) := by
  let F := nonbulkCombinatorialCost n B
  let r : ℝ := (2 ^ n : ℕ)
  have hF : 0 < F := nonbulkCombinatorialCost_pos n B
  have hr : 0 < r := by dsimp [r]; positivity
  have hden : 0 < ε * r * z := mul_pos (mul_pos hε hr) hz
  filter_upwards [eventually_ge_atTop (4 * Real.log F / (ε * r * z)),
    eventually_ge_atTop (0 : ℝ)] with L hL hL0
  intro m hm
  have hLL : 4 * Real.log F ≤ ε * r * z * L := by nlinarith [(div_le_iff₀ hden).mp hL]
  have hM := mul_le_mul_of_nonneg_left hm (mul_pos hε hr).le
  have hlog : Real.log F ≤ ε / 2 * r * m := by nlinarith
  have hb := mul_le_mul_of_nonneg_right hbudget hL0
  have hb' := mul_le_mul_of_nonneg_left hb hr.le
  have hcost : c * L * (2 ^ n * B : ℕ) ≤ ε / 2 * r * m := by
    rw [Nat.cast_mul]
    change c * L * (r * B) ≤ _
    nlinarith
  change F * _ ≤ _
  rw [← Real.exp_log hF, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith)

theorem eventual_scheduled_anchor_nonbulk_cost (n B : ℕ) (c ε z : ℝ)
    (hc : 0 ≤ c) (hε : 0 < ε) (hz : 0 < z)
    (hbudget : 4 * c * B ≤ ε * z) :
    ∀ᶠ L : ℝ in atTop, ∀ {I : Type*} [Fintype I]
      (role : I → CopyScheduleRole) (m : ℕ)
      (_word : Fin m ≃ {i : I // role i = .word}),
      z * L / 2 ≤ (m : ℝ) → Fintype.card {i : I // role i ≠ .word} ≤ B →
      ∀ mass : CopyScheduleH role n → ℝ,
      (∀ h : ScheduledNonbulkH role n, Real.exp (-c * L) ≤ mass h.val) →
      (Fintype.card (ScheduledNonbulkH role n)).factorial *
        (∏ h : ScheduledNonbulkH role n, (mass h.val)⁻¹) ≤
          Real.exp (ε * (2 ^ n : ℕ) * (m : ℝ)) := by
  let A : ℝ := (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ)
  have hA : 1 ≤ A := by
    have hp : 0 < (2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) := by positivity
    dsimp only [A]
    exact_mod_cast (Nat.succ_le_iff.mpr hp)
  filter_upwards [eventual_anchor_nonbulk_cost n B c ε z hc hε hz hbudget,
    eventually_ge_atTop (0 : ℝ)] with L hL hL0
  intro I instI role m word hm hB mass hmass
  have hnonneg : 0 ≤ (Fintype.card (ScheduledNonbulkH role n)).factorial *
      (∏ h : ScheduledNonbulkH role n, (mass h.val)⁻¹) := by
    apply mul_nonneg (by positivity)
    apply Finset.prod_nonneg
    intro h _
    exact inv_nonneg.mpr ((Real.exp_pos _).le.trans (hmass h))
  calc
    _ ≤ A * ((Fintype.card (ScheduledNonbulkH role n)).factorial *
        (∏ h : ScheduledNonbulkH role n, (mass h.val)⁻¹)) := by nlinarith
    _ ≤ nonbulkCombinatorialCost n B * Real.exp (c * L * (2 ^ n * B : ℕ)) := by
      have h := scheduled_nonbulk_harmonic_bound role n m B word hB mass c L
        (mul_nonneg hc hL0) hmass
      simpa only [A, mul_assoc] using h
    _ ≤ _ := hL m hm

/-- The actual H block only pays for original active nonword slots.
Negative word copies and the filler never enter this count. -/
theorem eventual_active_anchor_nonbulk_cost (n B : ℕ) (c ε z : ℝ)
    (hc : 0 ≤ c) (hε : 0 < ε) (hz : 0 < z)
    (hbudget : 4 * c * B ≤ ε * z) :
    ∀ᶠ L : ℝ in atTop, ∀ {I : Type*} [Fintype I]
      (role : I → CopyScheduleRole) (m : ℕ),
      z * L / 2 ≤ (m : ℝ) →
      Fintype.card {i : I // role i ≠ .word ∧ role i ≠ .outside} ≤ B →
      ∀ mass : CopyScheduleH role n → ℝ,
      (∀ h : ScheduledNonbulkH role n, Real.exp (-c * L) ≤ mass h.val) →
      (Fintype.card (ScheduledNonbulkH role n)).factorial *
        (∏ h : ScheduledNonbulkH role n, (mass h.val)⁻¹) ≤
          Real.exp (ε * (2 ^ n : ℕ) * (m : ℝ)) := by
  filter_upwards [eventual_anchor_nonbulk_cost n B c ε z hc hε hz hbudget,
    eventually_ge_atTop (0 : ℝ)] with L hL hL0
  intro I instI role m hm hB mass hmass
  have hN : Fintype.card (ScheduledNonbulkH role n) ≤ 2 ^ n * B :=
    (scheduledNonbulkH_card_active role n).trans (Nat.mul_le_mul_left _ hB)
  have hf : ((Fintype.card (ScheduledNonbulkH role n)).factorial : ℝ) ≤
      nonbulkCombinatorialCost n B := by
    have hfac : ((Fintype.card (ScheduledNonbulkH role n)).factorial : ℝ) ≤
        (2 ^ n * B).factorial := by exact_mod_cast Nat.factorial_le hN
    have hA : (1 : ℝ) ≤ (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ (2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) from
        Nat.one_le_iff_ne_zero.mpr (by positivity))
    unfold nonbulkCombinatorialCost
    exact hfac.trans (le_mul_of_one_le_left (by positivity) hA)
  have hp : (∏ h : ScheduledNonbulkH role n, (mass h.val)⁻¹) ≤
      Real.exp (c * L * (2 ^ n * B : ℕ)) := by
    calc
      _ ≤ ∏ _h : ScheduledNonbulkH role n, Real.exp (c * L) := by
        apply Finset.prod_le_prod₀
        · intro h _
          exact inv_nonneg.mpr ((Real.exp_pos _).le.trans (hmass h))
        · intro h _
          have he := one_div_le_one_div_of_le (Real.exp_pos (-c * L)) (hmass h)
          simpa only [one_div, show -c * L = -(c * L) by ring, Real.exp_neg,
            inv_inv] using he
      _ = Real.exp (c * L * Fintype.card (ScheduledNonbulkH role n)) := by
        simp only [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast hN)
        (mul_nonneg hc hL0))
  exact (mul_le_mul hf hp
    (Finset.prod_nonneg (fun h _ => inv_nonneg.mpr ((Real.exp_pos _).le.trans (hmass h))))
    (nonbulkCombinatorialCost_pos n B).le).trans (hL m hm)

/-- The required normalization budget is available at every sufficiently
large depth, from the actual cell-role bound of Section 4. -/
theorem eventual_anchor_role_budget (R c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ B : ℕ, (B : ℝ) ≤ cellRoleCountBound R k →
      4 * c * B ≤ ε * cellRoleScale k := by
  filter_upwards [eventually_cellRoleCountBound_le R (ε / (4 * c)) (by positivity)] with k hk B hB
  have hh := mul_le_mul_of_nonneg_left (hB.trans hk) (by positivity : 0 ≤ 4 * c)
  calc
    _ ≤ 4 * c * ((ε / (4 * c)) * cellRoleScale k) := hh
    _ = _ := by field_simp

end Ostmann

end OAI
