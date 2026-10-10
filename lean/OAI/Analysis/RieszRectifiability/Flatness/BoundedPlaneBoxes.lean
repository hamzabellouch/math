import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.OpenPlaneBoxes

namespace OAI

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

def exhaustionBox (ι : Type*) (H : ℕ) : Box ι where
  lower := fun _ => -((H : ℝ) + 1)
  upper := fun _ => (H : ℝ) + 1
  lower_lt_upper := by
    intro i
    have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
    linarith

def planeBoxOuterRadius (K : ℝ≥0) (H : ℕ) : ℝ := ((K : ℝ) + 1) * ((H : ℝ) + 1)

def boundedProjectionRegion {ι : Type*} {d : ℕ}
    (π : Ambient d → ι → ℝ) (a : Ambient d) (K : ℝ≥0) (H : ℕ) : Set (Ambient d) :=
  openProjectionBox (exhaustionBox ι H) π ∩ ball a (planeBoxOuterRadius K H)

theorem exhaustionBox_dist_zero_le {ι : Type*} [Fintype ι] (H : ℕ) (u : ι → ℝ)
    (hu : u ∈ exhaustionBox ι H) : dist u 0 ≤ (H : ℝ) + 1 := by
  apply (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ H + 1)).mpr
  intro i
  have hi := hu i
  change -((H : ℝ) + 1) < u i ∧ u i ≤ (H : ℝ) + 1 at hi
  simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using! abs_le.mpr ⟨hi.1.le, hi.2⟩

theorem mem_exhaustionBox_Ioo_of_norm_lt {ι : Type*} [Fintype ι]
    (H : ℕ) (u : ι → ℝ) (hu : ‖u‖ < (H : ℝ) + 1) : u ∈ Box.Ioo (exhaustionBox ι H) := by
  intro i _
  change -((H : ℝ) + 1) < u i ∧ u i < (H : ℝ) + 1
  apply abs_lt.mp
  exact (show |u i| ≤ ‖u‖ by simpa only [Real.norm_eq_abs] using! norm_le_pi_norm u i).trans_lt hu

theorem planeBoxOuterRadius_pos (K : ℝ≥0) (H : ℕ) : 0 < planeBoxOuterRadius K H := by
  unfold planeBoxOuterRadius
  positivity

theorem exhaustionBox_image_mem_outerBall {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (K : ℝ≥0) (he : LipschitzWith K e)
    (H : ℕ) (u : ι → ℝ) (hu : u ∈ exhaustionBox ι H) :
    e u ∈ ball (e 0) (planeBoxOuterRadius K H) := by
  apply mem_ball.mpr
  have hdist := (he.dist_le_mul u 0).trans
    (mul_le_mul_of_nonneg_left (exhaustionBox_dist_zero_le H u hu) K.coe_nonneg)
  dsimp [planeBoxOuterRadius]
  nlinarith

theorem boundedProjectionRegion_isOpen {ι : Type*} [Fintype ι] {d : ℕ}
    (π : Ambient d → ι → ℝ) (hπ : Continuous π) (a : Ambient d) (K : ℝ≥0) (H : ℕ) :
    IsOpen (boundedProjectionRegion π a K H) :=
  (openProjectionBox_isOpen (exhaustionBox ι H) π hπ).inter isOpen_ball

theorem boundedProjectionRegion_cover {ι : Type*} [Fintype ι] {d : ℕ}
    (π : Ambient d → ι → ℝ) (a : Ambient d) (K : ℝ≥0) (x : Ambient d) :
    ∃ H : ℕ, x ∈ boundedProjectionRegion π a K H := by
  obtain ⟨H, hH⟩ := exists_nat_gt (max ‖π x‖ (dist x a))
  have hnorm : ‖π x‖ < (H : ℝ) + 1 := by linarith [le_max_left ‖π x‖ (dist x a)]
  have hdist : dist x a < (H : ℝ) + 1 := by linarith [le_max_right ‖π x‖ (dist x a)]
  refine ⟨H, mem_exhaustionBox_Ioo_of_norm_lt H (π x) hnorm, ?_⟩
  apply mem_ball.mpr
  exact hdist.trans_le (by unfold planeBoxOuterRadius; nlinarith [K.coe_nonneg])

theorem boundedProjectionRegion_finite {ι : Type*} {d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (π : Ambient d → ι → ℝ) (a : Ambient d) (K : ℝ≥0) (H : ℕ) :
    IsFiniteMeasure (μ.restrict (boundedProjectionRegion π a K H)) := by
  apply isFiniteMeasure_restrict.mpr
  apply ne_of_lt
  apply (measure_mono (show boundedProjectionRegion π a K H ⊆
    closedBall a (planeBoxOuterRadius K H) from fun _ hx => mem_closedBall.mpr hx.2.le)).trans_lt
  exact (isCompact_closedBall a (planeBoxOuterRadius K H)).measure_lt_top

def boundedProjectionFiniteMeasure {ι : Type*} {d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (π : Ambient d → ι → ℝ) (a : Ambient d) (K : ℝ≥0) (H : ℕ) : FiniteMeasure (Ambient d) :=
  ⟨μ.restrict (boundedProjectionRegion π a K H), boundedProjectionRegion_finite μ π a K H⟩

theorem coordinatePlaneMeasure_restrict_boundedRegion {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K : ℝ≥0) (he : LipschitzWith K e) (hπ : Continuous π) (hleft : LeftInverse π e) (H : ℕ) :
    (coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H) =
      boxPlaneMeasure (exhaustionBox ι H) e := by
  have hpre : e ⁻¹' boundedProjectionRegion π (e 0) K H = Box.Ioo (exhaustionBox ι H) := by
    ext u
    change (π (e u) ∈ Box.Ioo (exhaustionBox ι H) ∧
      e u ∈ ball (e 0) (planeBoxOuterRadius K H)) ↔ u ∈ Box.Ioo (exhaustionBox ι H)
    rw [hleft u]
    exact ⟨And.left, fun hu => ⟨hu, exhaustionBox_image_mem_outerBall e K he H u
      ((exhaustionBox ι H).Ioo_subset_coe hu)⟩⟩
  rw [coordinatePlaneMeasure, Measure.restrict_map he.continuous.measurable
    (boundedProjectionRegion_isOpen π hπ (e 0) K H).measurableSet, hpre,
    Measure.restrict_congr_set ((exhaustionBox ι H).Ioo_ae_eq_Icc.trans
      (exhaustionBox ι H).coe_ae_eq_Icc.symm)]
  rfl

theorem boundedProjectionRegion_ae_coordinates {ι : Type*} [Fintype ι] {d : ℕ}
    (μ : Measure (Ambient d)) (π : Ambient d → ι → ℝ) (hπ : Continuous π)
    (a : Ambient d) (K : ℝ≥0) (H : ℕ) :
    ∀ᵐ x ∂μ.restrict (boundedProjectionRegion π a K H), π x ∈ exhaustionBox ι H := by
  filter_upwards [ae_restrict_mem (boundedProjectionRegion_isOpen π hπ a K H).measurableSet]
    with x hx
  exact (exhaustionBox ι H).Ioo_subset_coe hx.1

end

end RieszRectifiability

end OAI
