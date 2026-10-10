import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.PlanarPullbackMeasure
import OAI.Analysis.RieszRectifiability.Limits.CompactSmoothAnnularKernel
import OAI.Analysis.RieszRectifiability.Limits.VaryingCompactTests
import OAI.Analysis.RieszRectifiability.Foundations.SmoothAnnularIntegrability

namespace OAI

/-!
# Smooth annular transforms with varying centers

Converging centers yield uniform convergence of the scalar annular tests and an
eventual common compact support. Together with uniform growth, these estimates
pass the smooth annular transform through weak limits of measures.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped CompactlySupported ENNReal

theorem scalarSmoothAnnularTest_center_uniform {d : ℕ} (n : ℕ) (e : Ambient d)
    (a : ℕ → Ambient d) (b : Ambient d) (ha : Tendsto a atTop (𝓝 b))
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x,
      |scalarSmoothAnnularTest n e (a j) r R hr hrR x -
        scalarSmoothAnnularTest n e b r R hr hrR x| < ε := by
  let F := scalarSmoothAnnularTest n e (0 : Ambient d) r R hr hrR
  have hF := F.hasCompactSupport.uniformContinuous_of_continuous F.continuous
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp hF ε hε
  filter_upwards [Metric.tendsto_nhds.mp ha δ hδ] with j hj
  intro x
  have hd : dist (x - a j) (x - b) < δ := by
    simpa only [dist_sub_left] using! hj
  have ht := hmod hd
  change |inner ℝ e (smoothAnnularKernel n (a j) r R hr (hr.trans_le hrR) x) -
    inner ℝ e (smoothAnnularKernel n b r R hr (hr.trans_le hrR) x)| < ε
  rw [smoothAnnularKernel_translate n (a j), smoothAnnularKernel_translate n b]
  exact ht

theorem scalarSmoothAnnularTest_common_support {d : ℕ} (n : ℕ) (e : Ambient d)
    (a : ℕ → Ambient d) (b : Ambient d) (ha : Tendsto a atTop (𝓝 b))
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    ∀ᶠ j in atTop, ∀ x, x ∉ ball b (2 * R + 2) →
      scalarSmoothAnnularTest n e (a j) r R hr hrR x = 0 ∧
        scalarSmoothAnnularTest n e b r R hr hrR x = 0 := by
  filter_upwards [Metric.tendsto_nhds.mp ha 1 zero_lt_one] with j hj
  intro x hx
  have hxb : 2 * R + 2 ≤ dist x b := le_of_not_gt hx
  have hxa : 2 * R ≤ dist x (a j) := by
    have ht := dist_triangle x (a j) b
    linarith
  constructor
  · change inner ℝ e (smoothAnnularKernel n (a j) r R hr (hr.trans_le hrR) x) = 0
    rw [smoothAnnularKernel_zero_far n (a j) r R hr hrR x hxa, inner_zero_right]
  · change inner ℝ e (smoothAnnularKernel n b r R hr (hr.trans_le hrR) x) = 0
    rw [smoothAnnularKernel_zero_far n b r R hr hrR x (by linarith), inner_zero_right]

theorem scalarSmoothAnnularTest_integral {d : ℕ} (n : ℕ) (e a : Ambient d)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    (∫ x, scalarSmoothAnnularTest n e a r R hr hrR x ∂μ) =
      inner ℝ e (smoothAnnularTransform n μ a r R hr (hr.trans_le hrR)) := by
  have hi := (smoothAnnularKernel_continuous n a r R hr hrR).integrable_of_hasCompactSupport
    (smoothAnnularKernel_hasCompactSupport n a r R hr (hr.trans_le hrR)) (μ := μ)
  exact (innerSL ℝ e).integral_comp_comm hi

theorem smoothAnnularTransform_directional_tendsto {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts ν] (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (hlocal : CompactTestConvergence μ ν) (e : Ambient d)
    (a : ℕ → Ambient d) (b : Ambient d) (ha : Tendsto a atTop (𝓝 b))
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    Tendsto (fun j => inner ℝ e
      (smoothAnnularTransform n (μ j) (a j) r R hr (hr.trans_le hrR))) atTop
      (𝓝 (inner ℝ e (smoothAnnularTransform n ν b r R hr (hr.trans_le hrR)))) := by
  let (j : ℕ) : IsFiniteMeasureOnCompacts (μ j) := globalGrowth_finite_on_compacts G (μ j) (hg j)
  have hR : 0 < 2 * R + 2 := by linarith
  have hG : 0 ≤ G := (hg 0).1
  have hs : ∀ᶠ j in atTop, (μ j) (ball b (2 * R + 2)) < ∞ ∧
      (μ j).real (ball b (2 * R + 2)) ≤ G * (2 * R + 2) ^ n ∧
      ∀ x, x ∉ ball b (2 * R + 2) →
        scalarSmoothAnnularTest n e (a j) r R hr hrR x = 0 ∧
          scalarSmoothAnnularTest n e b r R hr hrR x = 0 := by
    filter_upwards [scalarSmoothAnnularTest_common_support n e a b ha r R hr hrR] with j hj
    have hm := (hg j).2 b (2 * R + 2) hR
    exact ⟨hm.trans_lt ENNReal.ofReal_lt_top,
      ENNReal.toReal_le_of_le_ofReal (by positivity) hm, hj⟩
  have ht := compactTestConvergence_varying_tests μ ν hlocal
    (fun j => scalarSmoothAnnularTest n e (a j) r R hr hrR)
    (scalarSmoothAnnularTest n e b r R hr hrR) (ball b (2 * R + 2))
    (G * (2 * R + 2) ^ n) (by positivity) hs
    (scalarSmoothAnnularTest_center_uniform n e a b ha r R hr hrR)
  simpa only [scalarSmoothAnnularTest_integral] using! ht

theorem smoothAnnularTransform_bound_of_center_limit {d : ℕ} (n : ℕ) (G B : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts ν] (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (hlocal : CompactTestConvergence μ ν)
    (a : ℕ → Ambient d) (b : Ambient d) (ha : Tendsto a atTop (𝓝 b))
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (hb : ∀ᶠ j in atTop, ‖smoothAnnularTransform n (μ j) (a j) r R hr (hr.trans_le hrR)‖ ≤ B) :
    ‖smoothAnnularTransform n ν b r R hr (hr.trans_le hrR)‖ ≤ B := by
  obtain ⟨e, he, heq⟩ := exists_unit_bounded_norm_direction
    (smoothAnnularTransform n ν b r R hr (hr.trans_le hrR))
  rw [← heq]
  apply le_of_tendsto (smoothAnnularTransform_directional_tendsto n G μ ν hg hlocal e a b ha r R hr hrR)
  filter_upwards [hb] with j hj
  exact (real_inner_le_norm _ _).trans
    ((mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans (by simpa only [one_mul] using! hj))

end

end RieszRectifiability

end OAI
