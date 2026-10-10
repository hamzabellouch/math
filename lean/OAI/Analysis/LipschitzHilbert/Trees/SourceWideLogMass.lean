import OAI.Analysis.LipschitzHilbert.Trees.SourceWeightPointwiseBudget
import OAI.Analysis.LipschitzHilbert.Phase.SourcePhaseParameters

namespace OAI

/-! The manuscript's full disparity window reaches log ratio = 2L.
Its polynomial top-count factor therefore needs a third logarithmic
unit. The same phase subpower bound survives this extra fixed unit. -/
noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert
open PhaseCombinatorics

theorem eventually_count_log_bound_wide (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ n N : ℝ, n ≤ L^C*N → 0 < N → Real.log N ≤ 2*L →
      Real.log (max 1 n) ≤ 3*L := by
  have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero C 1 (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with L hL hsmall
  intro n N hn hN hlog
  have hNexp : N ≤ Real.exp (2*L) := (Real.log_le_iff_le_exp hN).mp hlog
  have hpoly : L^C ≤ Real.exp L := by
    have h := mul_le_mul_of_nonneg_right hsmall.le (Real.exp_pos L).le
    simpa only [one_mul,neg_mul,one_mul,mul_assoc,← Real.exp_add,neg_add_cancel,
      Real.exp_zero,mul_one] using h
  have hexp : L^C*N ≤ Real.exp (3*L) := by
    calc
      _ ≤ Real.exp L*Real.exp (2*L) := mul_le_mul hpoly hNexp hN.le (Real.exp_pos _).le
      _ = _ := by rw [←Real.exp_add]; congr 1; ring
  have hmax : max 1 n ≤ Real.exp (3*L) := max_le
    (Real.one_le_exp (by linarith)) (hn.trans hexp)
  exact (Real.log_le_iff_le_exp (lt_of_lt_of_le zero_lt_one (le_max_left 1 n))).mpr hmax


theorem source_phase_mass_bound_wide {D L N : ℝ}
    (hD : 1 ≤ D) (hL : 1 ≤ L) (hN : 0 < N) (hlogN : Real.log N ≤ 3 * L) :
    N ^ phaseMu D (Real.sqrt L) ≤ Real.exp (4 * Real.sqrt L) := by
  have hL0 : 0 ≤ L := by linarith
  have hp : 0 < Real.sqrt L := Real.sqrt_pos.2 (by linarith)
  have hμ := phaseMu_positive_le hD hp
  have hsq := Real.sq_sqrt hL0
  rw [Real.rpow_def_of_pos hN]
  apply Real.exp_le_exp.mpr
  calc
    Real.log N * phaseMu D (Real.sqrt L) ≤ (3 * L) * phaseMu D (Real.sqrt L) :=
      mul_le_mul_of_nonneg_right hlogN hμ.1.le
    _ ≤ (3 * L) * ((4 / 3 : ℝ) / Real.sqrt L) :=
      mul_le_mul_of_nonneg_left hμ.2 (by positivity)
    _ = (4 : ℝ) * Real.sqrt L := by
      field_simp [hp.ne']
      nlinarith
    _ ≤ 4 * Real.sqrt L := by nlinarith [Real.sqrt_nonneg L]

theorem eventually_source_subpower_amplitude_wide (C δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, ∀ D N : ℝ, 1 ≤ D → 0 < N → Real.log N ≤ 3 * L →
      L ^ C * (1 + N ^ phaseMu D (Real.sqrt L)) ≤ SourceParameters.step L ^ δ := by
  have hpow := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)
  have hlog : Tendsto (fun L : ℝ => Real.log L / L ^ (7 / 10 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)).tendsto_div_nhds_zero
  have hroot : Tendsto (fun L : ℝ => Real.sqrt L / L ^ (7 / 10 : ℝ)) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 5)
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hL]
    norm_num
  have hconst : Tendsto (fun L : ℝ => Real.log 2 / L ^ (7 / 10 : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_const_nhds (x := Real.log 2)).mul (tendsto_inv_atTop_zero.comp hpow)
  have hsum := ((hlog.const_mul C).add hconst).add (hroot.const_mul 4)
  simp only [mul_zero, add_zero] at hsum
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsum.eventually (gt_mem_nhds hδ)] with L hL hsmall
  intro D N hD hN hlogN
  have hL0 : 0 < L := by linarith
  have hpower : 0 < L ^ (7 / 10 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hbudget : C * Real.log L + Real.log 2 + 4 * Real.sqrt L ≤ δ * L ^ (7 / 10 : ℝ) := by
    apply (div_le_iff₀ hpower).mp
    convert hsmall.le using 1
    ring
  have hmass := source_phase_mass_bound_wide hD hL hN hlogN
  have hone : 1 ≤ Real.exp (4 * Real.sqrt L) := Real.one_le_exp (by positivity)
  calc
    _ ≤ L ^ C * (2 * Real.exp (4 * Real.sqrt L)) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hL0.le _)
    _ = Real.exp (C * Real.log L + Real.log 2 + 4 * Real.sqrt L) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
        Real.rpow_def_of_pos hL0]
      rw [mul_comm C (Real.log L)]
      ring
    _ ≤ Real.exp (δ * L ^ (7 / 10 : ℝ)) := Real.exp_le_exp.mpr hbudget
    _ ≤ SourceParameters.step L ^ δ := by
      rw [Real.rpow_def_of_pos (SourceParameters.step_pos L)]
      apply Real.exp_le_exp.mpr
      exact (mul_le_mul_of_nonneg_left (SourceParameters.log_step_bounds hL0.le).1 hδ.le).trans_eq
        (mul_comm δ _)


theorem eventually_source_amplitude_squared_decay_wide (C γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ L : ℝ in atTop, ∀ D N : ℝ, 1 ≤ D → 0 < N → Real.log N ≤ 3 * L →
      (L ^ C * (1 + N ^ phaseMu D (Real.sqrt L))) ^ 2 *
        SourceParameters.step L ^ (-γ) ≤ SourceParameters.step L ^ (-γ / 2) := by
  have h := eventually_source_subpower_amplitude_wide C (γ / 4) (by positivity)
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with L hL hL0
  intro D N hD hN hlogN
  have hbound := hL D N hD hN hlogN
  have hnonneg : 0 ≤ L ^ C * (1 + N ^ phaseMu D (Real.sqrt L)) := by positivity
  have hpow : 0 ≤ SourceParameters.step L ^ (γ / 4) :=
    Real.rpow_nonneg (SourceParameters.step_pos L).le _
  have hsquare : (L ^ C * (1 + N ^ phaseMu D (Real.sqrt L))) ^ 2 ≤
      (SourceParameters.step L ^ (γ / 4)) ^ 2 := by nlinarith
  calc
    _ ≤ (SourceParameters.step L ^ (γ / 4)) ^ 2 * SourceParameters.step L ^ (-γ) :=
      mul_le_mul_of_nonneg_right hsquare (Real.rpow_nonneg (SourceParameters.step_pos L).le _)
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (SourceParameters.step_pos L).le,
        ← Real.rpow_add (SourceParameters.step_pos L)]
      congr 1
      push_cast
      ring

end LipschitzHilbert

end

end OAI
