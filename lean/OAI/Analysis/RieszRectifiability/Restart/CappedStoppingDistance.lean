import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open Set Metric

def cappedStoppingDistance {ι X : Type*} [PseudoMetricSpace X]
    (R : ℝ) (c : ι → X) (r : ι → ℝ) (x : X) : ℝ :=
  ⨅ i : Option ι, match i with
    | none => R
    | some i => dist x (c i) + r i

theorem cappedStoppingDistance_bddBelow {ι X : Type*} [PseudoMetricSpace X]
    (R : ℝ) (c : ι → X) (r : ι → ℝ)
    (hR : 0 ≤ R) (hr : ∀ i : ι, 0 ≤ r i) (x : X) :
    BddBelow (range (fun i : Option ι => match i with
      | none => R
      | some i => dist x (c i) + r i)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨i, rfl⟩
  cases i with
  | none => exact hR
  | some i => exact add_nonneg dist_nonneg (hr i)

theorem cappedStoppingDistance_nonneg {ι X : Type*} [PseudoMetricSpace X]
    (R : ℝ) (c : ι → X) (r : ι → ℝ)
    (hR : 0 ≤ R) (hr : ∀ i : ι, 0 ≤ r i) (x : X) :
    0 ≤ cappedStoppingDistance R c r x := by
  apply le_ciInf
  intro i
  cases i with
  | none => exact hR
  | some i => exact add_nonneg dist_nonneg (hr i)

theorem cappedStoppingDistance_le_cap {ι X : Type*} [PseudoMetricSpace X]
    (R : ℝ) (c : ι → X) (r : ι → ℝ)
    (hR : 0 ≤ R) (hr : ∀ i : ι, 0 ≤ r i) (x : X) :
    cappedStoppingDistance R c r x ≤ R := by
  exact ciInf_le (cappedStoppingDistance_bddBelow R c r hR hr x) none

theorem cappedStoppingDistance_le_center_radius {ι X : Type*} [PseudoMetricSpace X]
    (R : ℝ) (c : ι → X) (r : ι → ℝ)
    (hR : 0 ≤ R) (hr : ∀ i : ι, 0 ≤ r i) (x : X) (i : ι) :
    cappedStoppingDistance R c r x ≤ dist x (c i) + r i := by
  exact ciInf_le (cappedStoppingDistance_bddBelow R c r hR hr x) (some i)

theorem cappedStoppingDistance_le_add_dist {ι X : Type*} [PseudoMetricSpace X]
    (R : ℝ) (c : ι → X) (r : ι → ℝ)
    (hR : 0 ≤ R) (hr : ∀ i : ι, 0 ≤ r i) (x y : X) :
    cappedStoppingDistance R c r x ≤ cappedStoppingDistance R c r y + dist x y := by
  have hbound : cappedStoppingDistance R c r x - dist x y ≤
      cappedStoppingDistance R c r y := by
    apply le_ciInf
    intro i
    cases i with
    | none =>
      have hcap := cappedStoppingDistance_le_cap R c r hR hr x
      have hdist : 0 ≤ dist x y := dist_nonneg
      change cappedStoppingDistance R c r x - dist x y ≤ R
      linarith
    | some i =>
      have hcenter := cappedStoppingDistance_le_center_radius R c r hR hr x i
      have htriangle := dist_triangle x y (c i)
      change cappedStoppingDistance R c r x - dist x y ≤ dist y (c i) + r i
      linarith
  linarith

theorem cappedStoppingDistance_lipschitz {ι X : Type*} [PseudoMetricSpace X]
    (R : ℝ) (c : ι → X) (r : ι → ℝ)
    (hR : 0 ≤ R) (hr : ∀ i : ι, 0 ≤ r i) :
    LipschitzWith 1 (cappedStoppingDistance R c r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hxy := cappedStoppingDistance_le_add_dist R c r hR hr x y
  have hyx := cappedStoppingDistance_le_add_dist R c r hR hr y x
  rw [dist_comm y x] at hyx
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  apply abs_le.mpr
  constructor
  · linarith
  · linarith

theorem cappedStoppingDistance_pos_of_finite {ι X : Type*}
    [Finite ι] [PseudoMetricSpace X]
    (R : ℝ) (c : ι → X) (r : ι → ℝ)
    (hR : 0 < R) (hr : ∀ i : ι, 0 < r i) (x : X) :
    0 < cappedStoppingDistance R c r x := by
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite
    (f := fun i : Option ι => match i with
      | none => R
      | some i => dist x (c i) + r i)
  change 0 < ⨅ i : Option ι, match i with
    | none => R
    | some i => dist x (c i) + r i
  rw [← hi]
  cases i with
  | none => exact hR
  | some i => exact add_pos_of_nonneg_of_pos dist_nonneg (hr i)

end

end RieszRectifiability

end OAI
