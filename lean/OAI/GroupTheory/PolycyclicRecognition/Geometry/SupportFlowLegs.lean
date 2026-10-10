import OAI.GroupTheory.PolycyclicRecognition.Geometry.CoarseFlowBounds
import Mathlib.Analysis.Convex.Basic

namespace OAI

/-! # Actual one-parameter legs between support positions

The height along a translated one-parameter leg is the affine segment
between its endpoint heights. Its metric bound is uniform at scale `r`,
with one fixed additive constant for the finite-mesh argument.
-/

noncomputable section

namespace PolycyclicRecognition

variable {G W : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
  [AddCommGroup W] [Module ℝ W]

def flowLeg (d : ℝ → G) (x : G) (r t : ℝ) : G := x * d (r * t)

omit [PseudoMetricSpace G] [IsIsometricSMul G G] in
theorem flowLeg_endpoints (d : ℝ → G) (hzero : d 0 = 1) (x : G) (r : ℝ) :
    flowLeg d x r 0 = x ∧ flowLeg d x r 1 = x * d r := by
  simp [flowLeg, hzero]

theorem exists_flowLeg_coarse_bound (d : ℝ → G) (hd : Continuous d) (hzero : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : G) (r : ℝ), 0 ≤ r → ∀ s t : ℝ,
      dist (flowLeg d x r s) (flowLeg d x r t) ≤ C * r * |t - s| + C := by
  obtain ⟨C, hC, hb⟩ := continuous_flow_coarse_dist d hd hzero hmul
  refine ⟨C, hC, ?_⟩
  intro x r hr s t
  rw [flowLeg, flowLeg, dist_mul_left]
  have h := hb (r * s) (r * t)
  rw [← mul_sub, abs_mul, abs_of_nonneg hr] at h
  nlinarith [h]

omit [PseudoMetricSpace G] [IsIsometricSMul G G] in
theorem flowLeg_height (π : G →* Multiplicative W) (d : ℝ → G)
    {w₀ w₁ : W} (hd : ∀ t, (π (d t)).toAdd = t • (w₁ - w₀))
    {x : G} {r : ℝ} (hx : (π x).toAdd = r • w₀) (t : ℝ) :
    (π (flowLeg d x r t)).toAdd = r • (w₀ + t • (w₁ - w₀)) := by
  rw [flowLeg, map_mul]
  change (π x).toAdd + (π (d (r * t))).toAdd = _
  rw [hx, hd]
  module

omit [PseudoMetricSpace G] [IsIsometricSMul G G] in
/-- Convexity keeps every height on the leg inside the scaled template. -/
theorem flowLeg_height_mem (π : G →* Multiplicative W) (d : ℝ → G)
    {E : Set W} (hE : Convex ℝ E) {w₀ w₁ : W} (hw₀ : w₀ ∈ E) (hw₁ : w₁ ∈ E)
    (hd : ∀ t, (π (d t)).toAdd = t • (w₁ - w₀))
    {x : G} {r : ℝ} (hx : (π x).toAdd = r • w₀) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ w ∈ E, (π (flowLeg d x r t)).toAdd = r • w := by
  refine ⟨w₀ + t • (w₁ - w₀), hE.add_smul_sub_mem hw₀ hw₁ ht, ?_⟩
  exact flowLeg_height π d hd hx t

end PolycyclicRecognition

end

end OAI
