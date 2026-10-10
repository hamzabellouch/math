import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ADTruncations

namespace OAI

/-!
# Global growth from AD regularity

Finite total mass controls radii beyond an admissible scale, while AD regularity controls
smaller balls. Together with the infinite-diameter case, this yields global upper growth
for nontrivial support. Subsingleton support is treated separately through the absence of
admissible positive radii.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem globalGrowth_of_finite_ADRegular {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hAD : ADRegular n μ)
    (R : ℝ) (hR : AdmissibleRadius μ R) :
    ∃ G : ℝ, GlobalUpperGrowth n G μ := by
  obtain ⟨C, hC, hballs⟩ := hAD
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  let A : ℝ := μ.real univ / (R / 2) ^ n
  have hRhalf : 0 < R / 2 := half_pos hR.1
  have hA : 0 ≤ A := div_nonneg (measureReal_nonneg) (pow_nonneg hRhalf.le n)
  have hAeq : A * (R / 2) ^ n = μ.real univ :=
    div_mul_cancel₀ _ (pow_ne_zero n hRhalf.ne')
  refine ⟨C * 2 ^ n + A, add_nonneg (mul_nonneg hC0 (by positivity)) hA, ?_⟩
  intro x r hr
  by_cases hsmall : 2 * r ≤ R
  · by_cases hz : μ (ball x r) = 0
    · rw [hz]
      exact zero_le
    obtain ⟨z, hzball, hzsupport⟩ := μ.nonempty_inter_support_of_pos (pos_iff_ne_zero.mpr hz)
    have hsub : ball x r ⊆ ball z (2 * r) := by
      intro y hy
      change dist y z < 2 * r
      calc
        _ ≤ dist y x + dist x z := dist_triangle _ _ _
        _ < r + r := add_lt_add hy (by simpa only [mem_ball, dist_comm] using! hzball)
        _ = _ := by ring
    have hadmiss : AdmissibleRadius μ (2 * r) :=
      ⟨by positivity, (ENNReal.ofReal_le_ofReal hsmall).trans hR.2⟩
    calc
      μ (ball x r) ≤ μ (ball z (2 * r)) := measure_mono hsub
      _ ≤ ENNReal.ofReal (C * (2 * r) ^ n) := (hballs z hzsupport _ hadmiss).2
      _ ≤ ENNReal.ofReal ((C * 2 ^ n + A) * r ^ n) := by
        apply ENNReal.ofReal_le_ofReal
        rw [mul_pow]
        nlinarith [mul_nonneg hA (pow_nonneg hr.le n)]
  · have hrr : R / 2 ≤ r := by linarith
    have hpow : (R / 2) ^ n ≤ r ^ n := pow_le_pow_left₀ hRhalf.le hrr n
    have hmass : μ.real univ ≤ (C * 2 ^ n + A) * r ^ n := by
      calc
        _ = A * (R / 2) ^ n := hAeq.symm
        _ ≤ A * r ^ n := mul_le_mul_of_nonneg_left hpow hA
        _ ≤ _ := by
          have hca : A ≤ C * 2 ^ n + A := le_add_of_nonneg_left (mul_nonneg hC0 (by positivity))
          exact mul_le_mul_of_nonneg_right hca (pow_nonneg hr.le n)
    calc
      μ (ball x r) ≤ μ univ := measure_mono (subset_univ _)
      _ = ENNReal.ofReal (μ.real univ) := (ofReal_measureReal).symm
      _ ≤ ENNReal.ofReal ((C * 2 ^ n + A) * r ^ n) := ENNReal.ofReal_le_ofReal hmass

theorem globalGrowth_of_ADRegular_nontrivial {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (hAD : ADRegular n μ) (hsupport : μ.support.Nontrivial) :
    ∃ G : ℝ, GlobalUpperGrowth n G μ := by
  by_cases hd : ediam μ.support = ∞
  · exact adRegular_globalGrowth_of_ediam_top n μ hAD hd
  · let := finiteMeasure_of_bounded_support μ hd
    obtain ⟨x, hx, y, hy, hxy⟩ := hsupport
    have hR : AdmissibleRadius μ (dist x y) := by
      refine ⟨dist_pos.mpr hxy, ?_⟩
      rw [← edist_dist]
      exact edist_le_ediam_of_mem hx hy
    exact globalGrowth_of_finite_ADRegular n μ hAD _ hR

theorem uniformlyRectifiable_of_subsingleton_support {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) (hsub : μ.support.Subsingleton) : UniformlyRectifiable n μ := by
  refine ⟨1, by norm_num, 1, ?_⟩
  intro x hx r hr
  have hdiam : ediam μ.support = 0 := ediam_eq_zero_iff.mpr hsub
  have hzero : ENNReal.ofReal r = 0 := le_antisymm (hdiam ▸ hr.2) (zero_le)
  exact ((ENNReal.ofReal_pos.mpr hr.1).ne' hzero).elim

end

end RieszRectifiability

end OAI
