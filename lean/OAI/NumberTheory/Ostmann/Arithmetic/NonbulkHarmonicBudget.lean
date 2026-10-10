import OAI.NumberTheory.Ostmann.Construction.SurvivingSlotCount
import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkScale

namespace OAI

/-! # The nonbulk normalization costs only its actual surviving slots -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def nonbulkCombinatorialCost (n B : ℕ) : ℝ :=
  (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) * (2 ^ n * B).factorial

theorem nonbulkCombinatorialCost_pos (n B : ℕ) : 0 < nonbulkCombinatorialCost n B := by
  unfold nonbulkCombinatorialCost
  positivity

theorem eventual_nonbulk_depth_budget (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, 4 * c * (4 * (k : ℝ) + 8) ≤ ε * (k : ℝ) ^ 4 := by
  have hlarge : ∀ᶠ k : ℕ in atTop, 32 * c / ε ≤ (k : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hlarge, eventually_ge_atTop (2 : ℕ)] with k hk hk2
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hεk : 32 * c ≤ ε * k := by
    have h := (div_le_iff₀ hε).mp hk
    nlinarith
  have hp : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 4 :=
    pow_le_pow_right₀ (by linarith) (by omega)
  calc
    _ ≤ 32 * c * k := by nlinarith
    _ ≤ ε * (k : ℝ) ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hεk hk0]
    _ ≤ _ := mul_le_mul_of_nonneg_left hp hε.le

theorem scheduled_nonbulk_harmonic_bound {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m B : ℕ)
    (word : Fin m ≃ {i : I // role i = .word})
    (hB : Fintype.card {i : I // role i ≠ .word} ≤ B)
    (mass : CopyScheduleH role n → ℝ) (c L : ℝ) (hcL : 0 ≤ c * L)
    (hmass : ∀ h : ScheduledNonbulkH role n, Real.exp (-c * L) ≤ mass h.val) :
    (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
      (Fintype.card (ScheduledNonbulkH role n)).factorial *
      (∏ h : ScheduledNonbulkH role n, (mass h.val)⁻¹) ≤
        nonbulkCombinatorialCost n B * Real.exp (c * L * (2 ^ n * B : ℕ)) := by
  have hN : Fintype.card (ScheduledNonbulkH role n) ≤ 2 ^ n * B :=
    (scheduledNonbulkH_card_sharp role n m word).trans (Nat.mul_le_mul_left _ hB)
  have hf : ((Fintype.card (ScheduledNonbulkH role n)).factorial : ℝ) ≤
      (2 ^ n * B).factorial := by exact_mod_cast Nat.factorial_le hN
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
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast hN) hcL)
  unfold nonbulkCombinatorialCost
  exact mul_le_mul (mul_le_mul_of_nonneg_left hf (by positivity)) hp
    (Finset.prod_nonneg (fun h _ => inv_nonneg.mpr ((Real.exp_pos _).le.trans (hmass h))))
    (by positivity)

/-- The threshold is uniform in the growing slot type and word count. -/
theorem eventual_nonbulk_cost (n B k : ℕ) (hk : 0 < k) (c ε : ℝ)
    (_hc : 0 ≤ c) (hε : 0 < ε) (hbudget : 4 * c * B ≤ ε * (k : ℝ) ^ 4) :
    ∀ᶠ L : ℝ in atTop,
      nonbulkCombinatorialCost n B * Real.exp (c * L * (2 ^ n * B : ℕ)) ≤
        Real.exp (ε * (2 ^ n : ℕ) * (spectatorBulkCount k L : ℝ)) := by
  let F := nonbulkCombinatorialCost n B
  let r : ℝ := (2 ^ n : ℕ)
  have hr : 0 < r := by dsimp [r]; positivity
  have hF : 0 < F := nonbulkCombinatorialCost_pos n B
  have hk4 : 0 < (k : ℝ) ^ 4 := by positivity
  have ht := (spectatorBulkCount_tendsto k hk).eventually
    (eventually_ge_atTop (2 * Real.log F / (ε * r)))
  filter_upwards [ht, eventually_ge_atTop (4 / (k : ℝ) ^ 4),
    eventually_ge_atTop (0 : ℝ)] with L hL hscale hL0
  have hscale' : 4 ≤ (k : ℝ) ^ 4 * L := by
    simpa only [mul_comm L] using (div_le_iff₀ hk4).mp hscale
  have hhalf := spectatorBulkCount_half k L hscale'
  have hc : c * L * (2 ^ n * B : ℕ) ≤
      ε / 2 * r * (spectatorBulkCount k L : ℝ) := by
    have hb := mul_le_mul_of_nonneg_right hbudget hL0
    have hb' := mul_le_mul_of_nonneg_left hb hr.le
    have hm := mul_le_mul_of_nonneg_left hhalf (mul_nonneg hε.le hr.le)
    dsimp only [r] at hm hb' ⊢
    push_cast at hm hb' ⊢
    nlinarith
  have hlog : Real.log F ≤ ε / 2 * r * (spectatorBulkCount k L : ℝ) := by
    have hh := (div_le_iff₀ (mul_pos hε hr)).mp hL
    nlinarith
  change F * _ ≤ _
  rw [← Real.exp_log hF, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

theorem eventual_scheduled_nonbulk_cost (n B k : ℕ) (hk : 0 < k) (c ε : ℝ)
    (hc : 0 ≤ c) (hε : 0 < ε) (hbudget : 4 * c * B ≤ ε * (k : ℝ) ^ 4) :
    ∀ᶠ L : ℝ in atTop, ∀ {I : Type*} [Fintype I],
      ∀ (role : I → CopyScheduleRole)
        (_word : Fin (spectatorBulkCount k L) ≃ {i : I // role i = .word}),
      Fintype.card {i : I // role i ≠ .word} ≤ B →
      ∀ mass : CopyScheduleH role n → ℝ,
      (∀ h : ScheduledNonbulkH role n, Real.exp (-c * L) ≤ mass h.val) →
      (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
        (Fintype.card (ScheduledNonbulkH role n)).factorial *
        (∏ h : ScheduledNonbulkH role n, (mass h.val)⁻¹) ≤
          Real.exp (ε * (2 ^ n : ℕ) * (spectatorBulkCount k L : ℝ)) := by
  filter_upwards [eventual_nonbulk_cost n B k hk c ε hc hε hbudget,
    eventually_ge_atTop (0 : ℝ)] with L hcost hL
  intro I instI role word hB mass hmass
  exact (scheduled_nonbulk_harmonic_bound role n (spectatorBulkCount k L) B word hB
    mass c L (mul_nonneg hc hL) hmass).trans hcost

end Ostmann

end OAI
