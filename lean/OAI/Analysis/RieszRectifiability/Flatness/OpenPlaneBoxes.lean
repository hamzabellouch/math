import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.PlaneBoxGrowth

namespace OAI

/-!
# Open projection boxes and coordinate-plane measures

Pulling back open boxes along continuous coordinates gives open subsets of the
ambient space. Coordinate-plane measures satisfy upper growth bounds, which
in turn imply finiteness on compact sets.
-/

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

def coordinatePlaneMeasure {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) : Measure (Ambient d) := volume.map e

def openProjectionBox {ι X : Type*} (I : Box ι) (π : X → ι → ℝ) : Set X :=
  π ⁻¹' Box.Ioo I

theorem openProjectionBox_isOpen {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (I : Box ι) (π : X → ι → ℝ) (hπ : Continuous π) : IsOpen (openProjectionBox I π) :=
  (isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)).preimage hπ

theorem coordinatePlaneMeasure_restrict_openBox {ι : Type*} [Fintype ι] {d : ℕ}
    (I : Box ι) (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (he : Measurable e) (hπ : Continuous π) (hleft : LeftInverse π e) :
    (coordinatePlaneMeasure e).restrict (openProjectionBox I π) = boxPlaneMeasure I e := by
  have hpre : e ⁻¹' openProjectionBox I π = Box.Ioo I := by
    ext x
    simp only [openProjectionBox, mem_preimage, hleft x]
  rw [coordinatePlaneMeasure, Measure.restrict_map he (openProjectionBox_isOpen I π hπ).measurableSet,
    hpre, Measure.restrict_congr_set (I.Ioo_ae_eq_Icc.trans I.coe_ae_eq_Icc.symm)]
  rfl

theorem coordinatePlaneMeasure_upper_growth {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (he : Measurable e) (Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e) :
    GlobalUpperGrowth (Fintype.card ι) ((2 * (Q : ℝ)) ^ Fintype.card ι)
      (coordinatePlaneMeasure e) := by
  refine ⟨by positivity, ?_⟩
  intro x r hr
  rw [coordinatePlaneMeasure, Measure.map_apply he measurableSet_ball]
  calc
    volume (e ⁻¹' ball x r) ≤ volume (closedBall (π x) ((Q : ℝ) * r)) := by
      apply measure_mono
      intro u hu
      apply mem_closedBall.mpr
      have hu' : dist (e u) x < r := hu
      calc
        dist u (π x) = dist (π (e u)) (π x) := by rw [hleft u]
        _ ≤ (Q : ℝ) * dist (e u) x := hπ.dist_le_mul _ _
        _ ≤ (Q : ℝ) * r := mul_le_mul_of_nonneg_left hu'.le Q.coe_nonneg
    _ = ENNReal.ofReal ((2 * ((Q : ℝ) * r)) ^ Fintype.card ι) :=
      Real.volume_pi_closedBall (π x) (mul_nonneg Q.coe_nonneg hr.le)
    _ = ENNReal.ofReal ((2 * (Q : ℝ)) ^ Fintype.card ι * r ^ Fintype.card ι) := by
      congr 1
      rw [← mul_assoc, mul_pow]

theorem GlobalUpperGrowth.finite_on_compacts {d n : ℕ} {C : ℝ}
    {μ : Measure (Ambient d)} (h : GlobalUpperGrowth n C μ) : IsFiniteMeasureOnCompacts μ := by
  let : IsLocallyFiniteMeasure μ := ⟨fun x => ⟨ball x 1, ball_mem_nhds x (by norm_num),
    (h.2 x 1 (by norm_num)).trans_lt ENNReal.ofReal_lt_top⟩⟩
  infer_instance

theorem coordinatePlaneMeasure_finite_on_compacts {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (he : Measurable e) (Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e) :
    IsFiniteMeasureOnCompacts (coordinatePlaneMeasure e) :=
  (coordinatePlaneMeasure_upper_growth e π he Q hπ hleft).finite_on_compacts

end

end RieszRectifiability

end OAI
