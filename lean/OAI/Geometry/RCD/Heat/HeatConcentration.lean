import OAI.Geometry.RCD.Heat.HeatPointwiseDisplacement
import OAI.Geometry.RCD.Sobolev.GoodCutoffFromResolvent

namespace OAI

/-! # Short-time concentration of the actual heat measures

The constructed bounded-Laplacian cutoffs yield a dimensional escape
estimate. No continuous-kernel or pointwise Gaussian estimate is used.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem heatRadonMeasure_concentration_of_cutoff {q : X} {r C : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C)
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic q r C)
    (t : ℝ) (ht : 0 < t) :
    1 - t * (C / r^2) ≤
      (hX.heatRadonMeasure hn p t ht q).real (closedBall q (2*r)) := by
  let ν := hX.heatRadonMeasure hn p t ht q
  have hb (y : X) : |χ.weight y| ≤ (1 : ℝ≥0) := by
    rw [abs_of_nonneg (χ.bounds y).1]
    exact (χ.bounds y).2
  have hd := hX.heat_bounded_laplacian_pointwise hn p χ.sobolev χ.laplacian
    χ.weak_laplacian (div_nonneg hC (sq_nonneg _)) χ.laplacian_bound χ.weight
    χ.weight.continuous χ.representative 1 hb t ht q
  rw [χ.one q (mem_ball_self hr)] at hd
  have hu : (∫ y, χ.weight y ∂ν) ≤ ν.real (closedBall q (2*r)) := by
    calc
      _ ≤ ∫ y, (closedBall q (2*r)).indicator (fun _ => (1 : ℝ)) y ∂ν := by
        apply integral_mono (χ.weight.integrable ν)
          ((integrable_const (1 : ℝ)).indicator measurableSet_closedBall)
        intro y
        by_cases hy : y ∈ closedBall q (2*r)
        · simpa only [indicator_of_mem hy] using (χ.bounds y).2
        · rw [indicator_of_notMem hy, χ.zero y (by
            simpa only [mem_closedBall, dist_comm, not_le] using hy)]
      _ = _ := by
        rw [integral_indicator measurableSet_closedBall, integral_const]
        simp only [smul_eq_mul, mul_one,
          measureReal_restrict_apply MeasurableSet.univ, univ_inter]
  have hl := (abs_le.mp hd).1
  change -(t * (C/r^2)) ≤ (∫ y, χ.weight y ∂ν) - 1 at hl
  linarith

theorem heatRadonMeasure_concentration :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (q : X) (r : ℝ), 0 < r → -1 ≤ K*r^2 →
      ∀ (t : ℝ) (ht : 0 < t),
        1 - t * (C/r^2) ≤ (hX.heatRadonMeasure hn p t ht q).real (closedBall q (2*r)) := by
  obtain ⟨C, hC, hcut⟩ := hX.goodCutoffInput hn
  refine ⟨C, hC, ?_⟩
  intro q r hr hcurv t ht
  obtain ⟨χ⟩ := hcut q r hr hcurv
  exact hX.heatRadonMeasure_concentration_of_cutoff hn p hr (zero_le_one.trans hC) χ t ht

theorem heatRadonMeasure_half_mass :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (q : X) (r : ℝ), 0 < r → -1 ≤ K*r^2 →
      ∀ (t : ℝ) (ht : 0 < t), t ≤ r^2 / (2*C) →
        (1/2 : ℝ) ≤ (hX.heatRadonMeasure hn p t ht q).real (closedBall q (2*r)) := by
  obtain ⟨C, hC, hconc⟩ := hX.heatRadonMeasure_concentration hn p
  refine ⟨C, hC, ?_⟩
  intro q r hr hcurv t ht htime
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hmul : t * (2*C) ≤ r^2 := (le_div_iff₀ (by positivity : 0 < 2*C)).mp htime
  have hquot : t * (C/r^2) ≤ (1/2 : ℝ) := by
    rw [← mul_div_assoc, div_le_iff₀ (sq_pos_of_pos hr)]
    nlinarith
  exact (by linarith : (1/2 : ℝ) ≤ 1 - t*(C/r^2)).trans (hconc q r hr hcurv t ht)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
