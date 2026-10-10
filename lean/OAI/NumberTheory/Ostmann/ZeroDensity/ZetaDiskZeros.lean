import Mathlib.Analysis.Complex.JensenFormula
import OAI.NumberTheory.Ostmann.ZeroDensity.ZetaDiskBounds
import OAI.NumberTheory.Ostmann.ZeroDensity.FiniteAnalyticZeroFactors

namespace OAI

/-! # The actual finite zeta zero factors in a small right-half-plane disk -/

namespace Ostmann

open Complex Filter Metric Set MeromorphicOn
open scoped Classical BigOperators

noncomputable def zetaAtHeight (t : ℝ) (w : ℂ) : ℂ :=
  regularizedZeta (w + characterZeroCenter t)

theorem zetaAtHeight_analytic (t : ℝ) (w : ℂ) : AnalyticAt ℂ (zetaAtHeight t) w :=
  (regularizedZeta_analytic _).comp (analyticAt_id.add analyticAt_const)

theorem zetaAtHeight_lower_zero (t : ℝ) : 1 / 3 ≤ ‖zetaAtHeight t 0‖ := by
  simpa [zetaAtHeight] using regularizedZeta_lower_center t

theorem zetaAtHeight_order_ne_top (t : ℝ) (w : ℂ) :
    analyticOrderAt (zetaAtHeight t) w ≠ ⊤ := by
  intro he
  have hz := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero w (zetaAtHeight_analytic t)).mp he
  have hl := zetaAtHeight_lower_zero t
  rw [hz] at hl
  norm_num at hl

noncomputable def zetaDiskDivisor (t : ℝ) :=
  divisor (zetaAtHeight t) (closedBall 0 (3 / 2 : ℝ))

noncomputable def zetaDiskZeros (t : ℝ) : Finset ℂ :=
  ((zetaDiskDivisor t).finiteSupport (isCompact_closedBall 0 (3 / 2 : ℝ))).toFinset

theorem zetaDiskDivisor_eq (t : ℝ) (w : ℂ) (hw : ‖w‖ ≤ 3 / 2) :
    zetaDiskDivisor t w = (analyticOrderNatAt (zetaAtHeight t) w : ℤ) := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (zetaAtHeight_order_ne_top t w)
  rw [zetaDiskDivisor, AnalyticOnNhd.divisor_apply
    (fun z _ => zetaAtHeight_analytic t z) (by simpa using hw)]
  simp [analyticOrderNatAt, ← hn]

theorem mem_zetaDiskZeros (t : ℝ) (w : ℂ) :
    w ∈ zetaDiskZeros t ↔ ‖w‖ ≤ 3 / 2 ∧ zetaAtHeight t w = 0 := by
  change w ∈ ((zetaDiskDivisor t).finiteSupport (isCompact_closedBall _ _)).toFinset ↔ _
  rw [Set.Finite.mem_toFinset]
  change zetaDiskDivisor t w ≠ 0 ↔ _
  have hord : analyticOrderNatAt (zetaAtHeight t) w ≠ 0 ↔ zetaAtHeight t w = 0 := by
    have hh := (zetaAtHeight_analytic t w).analyticOrderAt_ne_zero
    rw [← Nat.cast_analyticOrderNatAt (zetaAtHeight_order_ne_top t w)] at hh
    simpa only [Nat.cast_ne_zero] using hh
  constructor
  · intro hn
    have hw : ‖w‖ ≤ 3 / 2 := by
      simpa using (zetaDiskDivisor t).supportWithinDomain hn
    exact ⟨hw, hord.mp (by simpa only [zetaDiskDivisor_eq t w hw, Int.natCast_ne_zero] using hn)⟩
  · rintro ⟨hw, hz⟩
    rw [zetaDiskDivisor_eq t w hw, Int.natCast_ne_zero]
    exact hord.mpr hz

theorem zetaAtHeight_disk_bound (t : ℝ) (w : ℂ) (hw : ‖w‖ ≤ 7 / 4) :
    ‖zetaAtHeight t w‖ ≤ 32 * (|t| + 2) ^ 2 := by
  apply regularizedZeta_disk_bound
  simpa [dist_eq_norm] using hw

theorem zetaDiskZeros_mass_bound (t : ℝ) :
    (∑ w ∈ zetaDiskZeros t, (analyticOrderNatAt (zetaAtHeight t) w : ℝ)) ≤
      Real.log (96 * (|t| + 2) ^ 2) / Real.log (7 / 6) := by
  let M := 32 * (|t| + 2) ^ 2
  have hM : 1 ≤ M := by dsimp [M]; nlinarith [abs_nonneg t, sq_nonneg (|t| + 2)]
  have hlo := zetaAtHeight_lower_zero t
  have hne : zetaAtHeight t 0 ≠ 0 := by intro he; rw [he, norm_zero] at hlo; linarith
  have ha : AnalyticOnNhd ℂ (zetaAtHeight t) (closedBall 0 |(7 / 4 : ℝ)|) :=
    fun z _ => zetaAtHeight_analytic t z
  have hj := ha.sum_divisor_le (r := (3 / 2 : ℝ)) (R := (7 / 4 : ℝ))
    (by norm_num) (by norm_num) hM hne (fun z hz =>
      zetaAtHeight_disk_bound t z (by
        simpa only [mem_closedBall, dist_zero_right, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 4)]
          using sphere_subset_closedBall hz))
  have hratio : M / ‖zetaAtHeight t 0‖ ≤ 3 * M := by
    apply (div_le_iff₀ (by linarith : 0 < ‖zetaAtHeight t 0‖)).mpr
    nlinarith
  have hlog := Real.log_le_log (div_pos (by linarith : 0 < M) (norm_pos_iff.mpr hne)) hratio
  have hlogp : 0 < Real.log (7 / 6 : ℝ) := Real.log_pos (by norm_num)
  have hmass : (∑ w ∈ zetaDiskZeros t, (analyticOrderNatAt (zetaAtHeight t) w : ℝ)) =
      ((∑ᶠ w, zetaDiskDivisor t w : ℤ) : ℝ) := by
    rw [finsum_eq_sum_of_support_subset (s := zetaDiskZeros t) _ (by
      intro w hw
      exact ((zetaDiskDivisor t).finiteSupport (isCompact_closedBall _ _)).mem_toFinset.mpr hw),
      Int.cast_sum]
    apply Finset.sum_congr rfl
    intro w hw
    rw [zetaDiskDivisor_eq t w ((mem_zetaDiskZeros t w).mp hw).1]
    simp
  rw [hmass]
  change ((∑ᶠ w, divisor (zetaAtHeight t) (closedBall 0 (3 / 2 : ℝ)) w : ℤ) : ℝ) ≤ _
  rw [show |(3 / 2 : ℝ)| = 3 / 2 by norm_num,
    show (7 / 4 : ℝ) / (3 / 2) = 7 / 6 by norm_num] at hj
  apply hj.trans
  convert div_le_div_of_nonneg_right hlog hlogp.le using 1
  dsimp [M]
  congr 2
  ring

end Ostmann

end OAI
