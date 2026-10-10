import OAI.MeasureTheory.Falconer.Shells.Shells
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable def sourceShellBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

noncomputable def sourceShellLowpass (n : ℕ) (r : ℝ) : ℝ := sourceShellBump (r/(2:ℝ)^n)
noncomputable def sourceShellBand (n : ℕ) (r : ℝ) : ℝ := sourceShellLowpass (n+1) r - sourceShellLowpass n r

theorem sourceShellLowpass_smooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (sourceShellLowpass n) :=
  sourceShellBump.contDiff.comp (contDiff_id.div_const _)

theorem sourceShellBand_smooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (sourceShellBand n) :=
  (sourceShellLowpass_smooth (n+1)).sub (sourceShellLowpass_smooth n)

theorem sourceShellLowpass_one (n : ℕ) {r : ℝ} (hr : |r| ≤ (2:ℝ)^n) :
    sourceShellLowpass n r = 1 := by
  apply sourceShellBump.one_of_mem_closedBall
  change dist (r/(2:ℝ)^n) 0 ≤ 1
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2^n)]
  exact (div_le_one (by positivity)).mpr hr

theorem sourceShellLowpass_zero (n : ℕ) {r : ℝ} (hr : (2:ℝ)^(n+1) ≤ |r|) :
    sourceShellLowpass n r = 0 := by
  apply sourceShellBump.zero_of_le_dist
  change 2 ≤ dist (r/(2:ℝ)^n) 0
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2^n)]
  apply (le_div_iff₀ (by positivity)).mpr
  simpa [pow_succ, mul_comm] using hr

theorem sourceShellBand_abs_le (n : ℕ) (r : ℝ) : |sourceShellBand n r| ≤ 1 := by
  have ha : 0 ≤ sourceShellLowpass (n+1) r := sourceShellBump.nonneg
  have hb : sourceShellLowpass (n+1) r ≤ 1 := sourceShellBump.le_one
  have hc : 0 ≤ sourceShellLowpass n r := sourceShellBump.nonneg
  have hd : sourceShellLowpass n r ≤ 1 := sourceShellBump.le_one
  rw [sourceShellBand, abs_le]
  constructor <;> linarith

theorem sourceShellBand_support_bounds (n : ℕ) {r : ℝ} (hr : sourceShellBand n r ≠ 0) :
    (2:ℝ)^n ≤ |r| ∧ |r| ≤ (2:ℝ)^(n+2) := by
  have hpow : (2:ℝ)^n ≤ 2^(n+1) := by rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n]
  constructor
  · by_contra h
    have hle : |r| ≤ (2:ℝ)^n := (not_le.mp h).le
    exact hr (by rw [sourceShellBand, sourceShellLowpass_one (n+1) (hle.trans hpow),
      sourceShellLowpass_one n hle, sub_self])
  · by_contra h
    have hle : (2:ℝ)^(n+2) ≤ |r| := (not_le.mp h).le
    have hpow' : (2:ℝ)^(n+1) ≤ 2^(n+2) := by
      exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)
    exact hr (by rw [sourceShellBand, sourceShellLowpass_zero (n+1) hle,
      sourceShellLowpass_zero n (hpow'.trans hle), sub_self])

theorem sourceShellBand_support (n : ℕ) : Function.support (sourceShellBand n) ⊆ dyadicShell (n+1) := by
  intro r hr
  have h := sourceShellBand_support_bounds n hr
  change (2:ℝ)^((↑(n+1 : ℕ):ℝ)-1) ≤ |r| ∧ |r| ≤ (2:ℝ)^((↑(n+1 : ℕ):ℝ)+1)
  rw [show (↑(n+1 : ℕ):ℝ)-1 = (n:ℝ) by push_cast; ring,
    show (↑(n+1 : ℕ):ℝ)+1 = (↑(n+2 : ℕ):ℝ) by push_cast; ring,
    Real.rpow_natCast, Real.rpow_natCast]
  exact h

theorem sourceShellBand_compact (n : ℕ) : HasCompactSupport (sourceShellBand n) :=
  HasCompactSupport.intro (dyadicShell_compact (n+1)) (fun r hr => by
    by_contra h
    exact hr (sourceShellBand_support n h))

theorem sourceShellPartition_telescope (n : ℕ) (r : ℝ) :
    sourceShellLowpass 0 r + ∑ k ∈ Finset.range n, sourceShellBand k r = sourceShellLowpass n r := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ← add_assoc, ih, sourceShellBand]; ring

theorem sourceShellLowpass_tendsto (r : ℝ) :
    Tendsto (fun n => sourceShellLowpass n r) atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => r/(2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))
  have h := sourceShellBump.continuous.continuousAt.tendsto.comp ht
  have hz : sourceShellBump (0:ℝ) = 1 := sourceShellBump.one_of_mem_closedBall (by
    change dist (0:ℝ) 0 ≤ 1
    norm_num)
  simpa only [sourceShellLowpass, hz, Function.comp_def] using h

end PlanarFalconer

end OAI
