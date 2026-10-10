import OAI.MeasureTheory.Falconer.Radial.ProjectionDensity
import OAI.MeasureTheory.Falconer.Radial.RadialContinuity

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable def sourceUnitDirection (θ : ℝ) : UnitCircle :=
  ⟨sourceDirection θ,norm_sourceDirection θ⟩

@[fun_prop] theorem continuous_sourceUnitDirection : Continuous sourceUnitDirection :=
  continuous_sourceDirection.subtype_mk _

noncomputable def sourceRadialVector (x y : Plane) : Plane :=
  if y=x then sourceDirection 0 else ‖y-x‖⁻¹ • (y-x)

theorem norm_sourceRadialVector (x y : Plane) : ‖sourceRadialVector x y‖ = 1 := by
  unfold sourceRadialVector
  split_ifs with h
  · exact norm_sourceDirection _
  · exact norm_smul_inv_norm (sub_ne_zero.mpr h)

noncomputable def sourceRadialUnit (x y : Plane) : UnitCircle :=
  ⟨sourceRadialVector x y,norm_sourceRadialVector x y⟩

@[fun_prop] theorem measurable_sourceRadialUnit (x : Plane) : Measurable (sourceRadialUnit x) := by
  apply Measurable.subtype_mk
  unfold sourceRadialVector
  exact Measurable.ite (measurableSet_singleton x) measurable_const (by fun_prop)

theorem radialOn_eq_sourceRadialUnit {A B : Set Plane} (hAB : Disjoint A B) (x : A) (y : B) :
    radialOn hAB x y = sourceRadialUnit x y := by
  apply Subtype.ext
  simp only [radialOn,sourceRadialUnit,sourceRadialVector]
  rw [ite_eq_right (sub_ne_zero.mp (disjoint_sub_ne_zero hAB x y))]

theorem sourceRadialUnit_ray (x : Plane) (θ : ℝ) {r : ℝ} (hr : 0 < r) :
    sourceRadialUnit x (x+r • sourceDirection θ) = sourceUnitDirection θ := by
  have hne : x+r • sourceDirection θ ≠ x := by
    intro h
    have hn := congrArg (fun y : Plane => ‖y-x‖) h
    simp only [add_sub_cancel_left,norm_smul,norm_sourceDirection,mul_one,sub_self,norm_zero,
      Real.norm_eq_abs,abs_of_pos hr] at hn
    exact hr.ne' hn
  apply Subtype.ext
  simp [sourceRadialUnit,sourceRadialVector,hne,sourceUnitDirection,norm_smul,
    norm_sourceDirection,Real.norm_eq_abs,abs_of_pos hr,smul_smul,hr.ne']

noncomputable def sourceRadialDensity (a : Plane → ℝ≥0∞) (x : Plane) (θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal r * a (x+r • sourceDirection θ)

@[fun_prop] theorem measurable_sourceRadialDensity (a : Plane → ℝ≥0∞)
    (ha : Measurable a) (x : Plane) : Measurable (sourceRadialDensity a x) := by
  unfold sourceRadialDensity
  have h : Measurable (fun p : ℝ × ℝ =>
    ENNReal.ofReal p.2 * a (x+p.2 • sourceDirection p.1)) := by fun_prop
  exact h.lintegral_prod_right'

theorem translated_plane_polar_lintegral (f : Plane → ℝ≥0∞) (hf : Measurable f) (x : Plane) :
    (∫⁻ θ in Ioc 0 (2*Real.pi), ∫⁻ r in Ioi (0:ℝ),
      ENNReal.ofReal r * f (x+r • sourceDirection θ)) = ∫⁻ y : Plane, f y := by
  exact (plane_polar_lintegral (fun y => f (x+y)) (by fun_prop)).trans
    (lintegral_add_left_eq_self (μ := (volume : Measure Plane)) f x)

theorem sourceRadialUnit_withDensity (a : Plane → ℝ≥0∞) (ha : Measurable a) (x : Plane) :
    (volume.withDensity a).map (sourceRadialUnit x) =
      ((volume.restrict (Ioc 0 (2*Real.pi))).withDensity (sourceRadialDensity a x)).map
        sourceUnitDirection := by
  ext S hS
  rw [Measure.map_apply (measurable_sourceRadialUnit x) hS,
    Measure.map_apply continuous_sourceUnitDirection.measurable hS,
    withDensity_apply _ (hS.preimage (measurable_sourceRadialUnit x)),
    withDensity_apply _ (hS.preimage continuous_sourceUnitDirection.measurable)]
  let F : Plane → ℝ≥0∞ := (sourceRadialUnit x ⁻¹' S).indicator a
  have hF : Measurable F := ha.indicator (hS.preimage (measurable_sourceRadialUnit x))
  rw [← lintegral_indicator (hS.preimage (measurable_sourceRadialUnit x))]
  rw [← translated_plane_polar_lintegral F hF x]
  rw [← lintegral_indicator (hS.preimage continuous_sourceUnitDirection.measurable)]
  apply lintegral_congr
  intro θ
  by_cases hθ : sourceUnitDirection θ ∈ S
  · simp only [Set.indicator_of_mem (show θ ∈ sourceUnitDirection ⁻¹' S from hθ)]
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hy : x+r • sourceDirection θ ∈ sourceRadialUnit x ⁻¹' S := by
      simpa only [mem_preimage,sourceRadialUnit_ray x θ hr] using hθ
    change _ * (sourceRadialUnit x ⁻¹' S).indicator a _ = _
    rw [Set.indicator_of_mem hy]
  · simp only [Set.indicator_of_notMem (show θ ∉ sourceUnitDirection ⁻¹' S from hθ)]
    calc
      _ = ∫⁻ r in Ioi (0:ℝ), (0 : ℝ≥0∞) := by
        apply lintegral_congr_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
        have hy : x+r • sourceDirection θ ∉ sourceRadialUnit x ⁻¹' S := by
          simpa only [mem_preimage,sourceRadialUnit_ray x θ hr] using hθ
        change _ * (sourceRadialUnit x ⁻¹' S).indicator a _ = 0
        rw [Set.indicator_of_notMem hy,mul_zero]
      _ = 0 := by simp

theorem sourceRadialDensity_le (a : Plane → ℝ≥0∞) (x : Plane) {D : ℝ}
    (hbound : ∀ y, a y ≠ 0 → dist y x ≤ D) (θ : ℝ) :
    sourceRadialDensity a x θ ≤ ENNReal.ofReal D * projectedDensity a θ (sourceProjection θ x) := by
  rw [projectedDensity_line]
  calc
    _ ≤ ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal D * a (x+r • sourceDirection θ) := by
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      change 0 < r at hr
      by_cases hz : a (x+r • sourceDirection θ) = 0
      · simp [hz]
      · apply mul_le_mul_left
        apply ENNReal.ofReal_le_ofReal
        have h := hbound (x+r • sourceDirection θ) hz
        simpa [dist_eq_norm,norm_smul,norm_sourceDirection,Real.norm_eq_abs,abs_of_pos hr] using h
    _ = ENNReal.ofReal D * ∫⁻ r in Ioi (0:ℝ), a (x+r • sourceDirection θ) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_right (lintegral_mono' Measure.restrict_le_self (le_refl _)) _

end PlanarFalconer

end OAI
