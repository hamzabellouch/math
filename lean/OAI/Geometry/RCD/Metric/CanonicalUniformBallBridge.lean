import OAI.Geometry.RCD.Heat.CanonicalUniformBridge
import OAI.Geometry.RCD.Heat.CanonicalRoughGaussianLower

namespace OAI

/-! # A short final heat step after a uniform-ball heat factor

The rough Gaussian estimate is used only for the final short step. The
preceding heat factor satisfies the sharp action lower limit.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonical_uniform_ball_bridge :
    ∃ c D : ℝ, 0 < c ∧ 0 < D ∧ ∀ (z : X) (r : ℝ), (hr : 0 < r) →
      ∀ (ν : Measure (closedBall z r)) [IsProbabilityMeasure ν],
      ν.map Subtype.val = uniformOn (hausdorff n X) (closedBall z r) →
      ∀ (s t : ℝ) (hs : 0 < s) (_ht : 0 < t), t ≤ 1 → ∀ x y : X, dist y z ≤ r →
      (c*(hausdorff n X).real (closedBall z r)/(hausdorff n X).real (ball z (r+1)))*
        Real.exp (-D*r^2/t)*hX.compactHeatFactor hn p ν 1 s hs x ≤
        hX.canonicalHeatKernel hn p (s+t) x y := by
  obtain ⟨c,D,hc,hD,hrough⟩ := hX.canonicalHeatKernel_rough_gaussian_lower hn p
  refine ⟨c,4*D,hc,by positivity,?_⟩
  intro z r hr ν _ hν s t hs ht ht1 x y hy
  let μ := hausdorff n X
  let V := μ.real (ball z (r+1))
  have hV : 0 < V := ENNReal.toReal_pos (hX.fullSupport z _ (by linarith)).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hS0 : 0 < μ.real (closedBall z r) := ENNReal.toReal_pos
    (ne_of_gt ((hX.fullSupport z r hr).trans_le (measure_mono ball_subset_closedBall)))
    (hX.finiteOnBounded _ isBounded_closedBall).ne
  have hh := hX.canonical_uniform_bridge hn p ν hν hS0 hs ht x y (by
    intro q hq
    have hqy : dist q y ≤ 2*r := by
      have hh := dist_triangle q z y
      have hqz : dist q z ≤ r := hq
      rw [dist_comm z y] at hh
      linarith
    have hdy : (dist q y)^2 ≤ 4*r^2 := by nlinarith [dist_nonneg (x := q) (y := y)]
    have hTy : 0 < μ.real (ball y (Real.sqrt t)) := ENNReal.toReal_pos
      (hX.fullSupport y _ (Real.sqrt_pos.mpr ht)).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
    have hsub : ball y (Real.sqrt t) ⊆ ball z (r+1) := by
      intro w hw
      have hroot : Real.sqrt t ≤ 1 := by nlinarith [Real.sq_sqrt ht.le,Real.sqrt_nonneg t]
      have hd := dist_triangle w y z
      have hw' : dist w y < Real.sqrt t := hw
      exact mem_ball.mpr (by linarith)
    have hvol : μ.real (ball y (Real.sqrt t)) ≤ V :=
      measureReal_mono hsub (hX.finiteOnBounded _ isBounded_ball).ne
    have hcoef : c/V ≤ c/μ.real (ball y (Real.sqrt t)) :=
      div_le_div_of_nonneg_left hc.le hTy hvol
    have hexp : -(4*D)*r^2/t ≤ -D*(dist q y)^2/t := by
      apply div_le_div_of_nonneg_right _ ht.le
      nlinarith
    exact (mul_le_mul hcoef (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le
      (div_nonneg hc.le hTy.le)).trans (hrough t ht ht1 q y))
  convert hh using 1
  dsimp only [V]
  ring

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
