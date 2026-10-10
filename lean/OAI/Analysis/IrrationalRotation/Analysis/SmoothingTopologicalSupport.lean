import OAI.Analysis.IrrationalRotation.Rotation.CircleSmoothing

namespace OAI

namespace InvariantProjection.Continuity

open MeasureTheory Set Metric
local notation "Circle" => AddCircle (1 : ℝ)
local notation "rep" => (fun x : Circle => (AddCircle.equivIco (1 : ℝ) 0 x : ℝ))

private theorem dist_coe_le_abs (u v : ℝ) :
    dist (u : Circle) (v : Circle) ≤ |u - v| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  exact QuotientAddGroup.norm_mk_le_norm

theorem tsupport_circleSmoothedDrop_subset_closedBall {a δ : ℝ} (C : ℝ)
    (ha : 0 ≤ a) (hδ : 0 < δ) :
    tsupport (circleSmoothedDrop C a δ) ⊆
      closedBall ((-a / 2 : ℝ) : Circle) (a / 2 + δ) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  have hu : rep x ∈ Ico (0 : ℝ) 1 := by
    simpa using (AddCircle.equivIco (1 : ℝ) 0 x).property
  have hfrac : Int.fract (rep x) = rep x := Int.fract_eq_self.mpr hu
  have hout : rep x ≤ δ ∨ 1 - a - δ ≤ rep x := by
    by_contra hn
    push Not at hn
    apply hx
    rw [circleSmoothedDrop_eq_representative]
    exact smoothedDrop_eq_zero_of_middle C ha hδ
      (by rw [hfrac]; linarith) (by rw [hfrac]; linarith)
  rcases hout with hl | hr
  · change dist x ((-a / 2 : ℝ) : Circle) ≤ _
    calc
      _ = dist ((rep x : ℝ) : Circle) ((-a / 2 : ℝ) : Circle) := by
        rw [AddCircle.coe_equivIco]
      _ ≤ |rep x - -a / 2| := dist_coe_le_abs _ _
      _ ≤ a / 2 + δ := by rw [abs_le]; constructor <;> linarith [hu.1]
  · have hrep : ((rep x - 1 : ℝ) : Circle) = x := by
      rw [AddCircle.coe_sub, AddCircle.coe_period, sub_zero, AddCircle.coe_equivIco]
    change dist x ((-a / 2 : ℝ) : Circle) ≤ _
    calc
      _ = dist ((rep x - 1 : ℝ) : Circle) ((-a / 2 : ℝ) : Circle) := by rw [hrep]
      _ ≤ |rep x - 1 - -a / 2| := dist_coe_le_abs _ _
      _ ≤ a / 2 + δ := by rw [abs_le]; constructor <;> linarith [hu.2]

theorem measure_tsupport_circleSmoothedDrop_le {a δ : ℝ} (C : ℝ)
    (ha : 0 ≤ a) (hδ : 0 < δ) :
    volume (tsupport (circleSmoothedDrop C a δ)) ≤ ENNReal.ofReal (a + 2 * δ) := by
  calc
    _ ≤ volume (closedBall ((-a / 2 : ℝ) : Circle) (a / 2 + δ)) :=
      measure_mono (tsupport_circleSmoothedDrop_subset_closedBall C ha hδ)
    _ ≤ ENNReal.ofReal (a + 2 * δ) := by
      rw [AddCircle.volume_closedBall]
      apply ENNReal.ofReal_le_ofReal
      calc
        min (1 : ℝ) (2 * (a / 2 + δ)) ≤ 2 * (a / 2 + δ) := min_le_right _ _
        _ = a + 2 * δ := by ring

theorem measure_tsupport_characterSmoothedDrop_le {a δ : ℝ} (C : ℝ)
    (ha : 0 ≤ a) (hδ : 0 < δ) {q : ℤ} (hq : q ≠ 0) :
    volume (tsupport (fun x : Circle => circleSmoothedDrop C a δ (q • x))) ≤
      ENNReal.ofReal (a + 2 * δ) := by
  have hp := Measure.measurePreserving_zsmul (volume : Measure Circle) hq
  calc
    _ ≤ volume ((fun x : Circle => q • x) ⁻¹' tsupport (circleSmoothedDrop C a δ)) :=
      measure_mono (tsupport_comp_subset_preimage _ (continuous_id.zsmul q))
    _ = volume (tsupport (circleSmoothedDrop C a δ)) :=
      hp.measure_preimage (isClosed_tsupport _).measurableSet.nullMeasurableSet
    _ ≤ _ := measure_tsupport_circleSmoothedDrop_le C ha hδ

end InvariantProjection.Continuity

end OAI
