import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalSchwartzContinuity

namespace OAI

/-!
# Truncated fractional Schwartz tests

Restricting the symmetric second-difference kernel to the closed exterior of a
ball gives measurable tests with uniform bounds in Schwartz seminorms. The
integrable full kernel dominates every truncation, so dominated convergence
recovers the fractional Schwartz test as the truncation radii tend to zero.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set

def fractionalSchwartzTruncatedTest (p : ℕ) (ε : ℝ)
    (g : 𝓢(Ambient (p + 1), ℂ)) (x : Ambient (p + 1)) : ℂ :=
  (-1 / 2 : ℝ) • (∫ h in closedExterior 0 ε, fractionalSchwartzKernel (p + 1) g x h)

theorem fractionalSchwartzTruncatedTest_measurable (p : ℕ) (ε : ℝ)
    (g : 𝓢(Ambient (p + 1), ℂ)) : Measurable (fractionalSchwartzTruncatedTest p ε g) := by
  have hm : Measurable (fun q : Ambient (p + 1) × Ambient (p + 1) =>
      fractionalSchwartzKernel (p + 1) g q.1 q.2) := by
    unfold fractionalSchwartzKernel symmetricSecondDifference inverseDistancePow
    fun_prop
  unfold fractionalSchwartzTruncatedTest
  simp_rw [RCLike.real_smul_eq_coe_mul]
  exact measurable_const.mul (hm.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure (Ambient (p + 1))).restrict (closedExterior 0 ε))).measurable

theorem fractionalSchwartzTruncatedTest_uniform_bound (p : ℕ) (ε : ℝ)
    (g : 𝓢(Ambient (p + 1), ℂ)) (x : Ambient (p + 1)) :
    ‖fractionalSchwartzTruncatedTest p ε g x‖ ≤
      4 * (((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal * 2 ^ (p + 1) * 2 ^ p) *
        SchwartzMap.seminorm ℝ 0 2 g +
      8 * (((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal * 2 ^ (p + 1)) *
        SchwartzMap.seminorm ℝ 0 0 g := by
  let K := fractionalSchwartzKernel (p + 1) g x
  have hi : Integrable K := fractionalSchwartzKernel_integrable p g x
  have hb := fractionalSchwartzKernel_integral_norm_bound p _ volume
    (volume_global_upper_growth (p + 1)) g x
  have hn := norm_integral_le_integral_norm (μ := volume.restrict (closedExterior 0 ε)) K
  have hr : (∫ h in closedExterior 0 ε, ‖K h‖) ≤ ∫ h, ‖K h‖ :=
    integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun h => norm_nonneg _) hi.norm
  unfold fractionalSchwartzTruncatedTest
  rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal]
  norm_num
  nlinarith [norm_nonneg (∫ h in closedExterior 0 ε, K h)]

theorem fractionalSchwartzTruncatedTest_tendsto (p : ℕ)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) :
    Tendsto (fun j => fractionalSchwartzTruncatedTest p (ε j) g x)
      atTop (𝓝 (fractionalSchwartzTest p g x)) := by
  let K := fractionalSchwartzKernel (p + 1) g x
  have hi : Integrable K := fractionalSchwartzKernel_integrable p g x
  have hK0 : K 0 = 0 := by
    dsimp [K, fractionalSchwartzKernel, inverseDistancePow]
    simp
  have hlim (h : Ambient (p + 1)) :
      Tendsto (fun j => (closedExterior 0 (ε j)).indicator K h) atTop (𝓝 (K h)) := by
    by_cases hh : h = 0
    · subst h
      have hz : (fun j => (closedExterior 0 (ε j)).indicator K 0) = fun _ : ℕ => (0 : ℂ) := by
        funext j
        by_cases hs : (0 : Ambient (p + 1)) ∈ closedExterior 0 (ε j)
        · exact (indicator_of_mem hs K).trans hK0
        · exact indicator_of_notMem hs K
      rw [hz, hK0]
      exact tendsto_const_nhds
    · have hp : 0 < ‖h‖ := norm_pos_iff.mpr hh
      apply tendsto_const_nhds.congr'
      filter_upwards [hε.eventually (gt_mem_nhds hp)] with j hj
      have hs : h ∈ closedExterior 0 (ε j) := by
        simpa only [closedExterior, mem_ofPred_eq, dist_zero_left] using! hj.le
      exact (indicator_of_mem hs K).symm
  have ht := tendsto_integral_of_dominated_convergence (fun h => ‖K h‖)
    (fun j => hi.aestronglyMeasurable.indicator (closedExterior_measurable 0 (ε j))) hi.norm
    (fun j => Eventually.of_forall fun h => norm_indicator_le_norm_self K h)
    (Eventually.of_forall hlim)
  have heq : (fun j => ∫ h in closedExterior 0 (ε j), K h) =
      fun j => ∫ h, (closedExterior 0 (ε j)).indicator K h := by
    funext j
    exact (integral_indicator (f := K) (closedExterior_measurable 0 (ε j))).symm
  change Tendsto (fun j => (-1 / 2 : ℝ) • (∫ h in closedExterior 0 (ε j), K h))
    atTop (𝓝 ((-1 / 2 : ℝ) • ∫ h, K h))
  change Tendsto (fun j => (-1 / 2 : ℝ) • ((fun j => ∫ h in closedExterior 0 (ε j), K h) j)) _ _
  rw [heq]
  exact ht.const_smul (-1 / 2 : ℝ)

end

end RieszRectifiability

end OAI
