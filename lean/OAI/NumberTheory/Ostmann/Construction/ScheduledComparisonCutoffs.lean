import OAI.NumberTheory.Ostmann.Construction.ScheduledPrimeCutoffs
import OAI.NumberTheory.Ostmann.Characters.CharacterBandCutoffs

namespace OAI

/-! # Integer cutoffs below the actual spectator band and above all finite frequencies -/
namespace Ostmann
open Filter

noncomputable def scheduledComparisonCutoff (L : ℝ) : ℕ :=
  ⌈Real.exp (Real.exp ((2 / 10000 : ℝ) * L))⌉₊

noncomputable def scheduledComparisonPrimeLo (L : ℝ) : ℕ :=
  ⌊Real.exp (Real.exp ((7 / 10000 : ℝ) * L))⌋₊

theorem eventual_scheduled_comparison_cutoffs (k N p₀ : ℕ) (A : ℕ → ℝ) :
    ∀ᶠ L : ℝ in atTop,
      p₀ ≤ scheduledComparisonCutoff L ∧
      scheduledComparisonCutoff L ≤ scheduledComparisonPrimeLo L ∧
      (scheduledComparisonPrimeLo L : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ∧
      (∀ p : ℕ, Real.exp (Real.exp ((4 / 10000 : ℝ) * L)) ≤ p →
        (p : ℝ) ≤ Real.exp (Real.exp ((6 / 10000 : ℝ) * L)) →
        scheduledComparisonCutoff L ≤ p ∧ p ≤ scheduledComparisonPrimeLo L) ∧
      (∀ n ≤ N, ∀ V : ℕ, (V : ℝ) ≤ Real.exp (A n * spectatorBulkCount k L) →
        V < scheduledComparisonCutoff L ∧ V ≤ scheduledComparisonPrimeLo L) := by
  have hgrow : Tendsto (fun L : ℝ => Real.exp (Real.exp ((2 / 10000 : ℝ) * L))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop (by norm_num)))
  filter_upwards [eventual_finite_frequency_band k N A (2 / 10000) (by norm_num),
    eventual_double_exp_integer_margin (2 / 10000) (4 / 10000) (by norm_num) (by norm_num),
    hgrow.eventually (eventually_ge_atTop (p₀ : ℝ)), eventually_gt_atTop (0 : ℝ)]
    with L hfreq hgap hp₀ hL
  have hcpos : 0 < (scheduledComparisonCutoff L : ℝ) := by
    exact_mod_cast (Nat.ceil_pos.mpr (Real.exp_pos _))
  have hc4 : (scheduledComparisonCutoff L : ℝ) ≤
      Real.exp (Real.exp ((4 / 10000 : ℝ) * L)) := by
    dsimp only [scheduledComparisonCutoff]
    linarith
  have h47 : Real.exp (Real.exp ((4 / 10000 : ℝ) * L)) ≤
      Real.exp (Real.exp ((7 / 10000 : ℝ) * L)) :=
    Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith))
  have hcut : scheduledComparisonCutoff L ≤ scheduledComparisonPrimeLo L :=
    Nat.le_floor (hc4.trans h47)
  refine ⟨?_, hcut, ?_, ?_, ?_⟩
  · exact_mod_cast hp₀.trans (Nat.le_ceil _)
  · exact (Nat.floor_le (Real.exp_nonneg _)).trans_lt
      (Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr (by linarith)))
  · intro p hp hpu
    constructor
    · exact_mod_cast hc4.trans hp
    · apply Nat.le_floor
      exact hpu.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith)))
  · intro n hn V hV
    have hv : (V : ℝ) < scheduledComparisonCutoff L :=
      (hV.trans_lt (hfreq n hn)).trans_le (Nat.le_ceil _)
    have hvNat : V < scheduledComparisonCutoff L := by exact_mod_cast hv
    exact ⟨hvNat, hvNat.le.trans hcut⟩

end Ostmann

end OAI
