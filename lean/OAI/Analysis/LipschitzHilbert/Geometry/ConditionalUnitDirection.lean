import OAI.Analysis.LipschitzHilbert.Estimates.ChartPullback
import OAI.Analysis.LipschitzHilbert.Estimates.ConditionalVariableEndpoints
import OAI.Analysis.LipschitzHilbert.Geometry.FiniteOutputCover
import OAI.Analysis.LipschitzHilbert.Estimates.ShortTransformMeasurable

namespace OAI

/-! Uniform L2 truncation bounds for unit vector fields with a fixed small
Lipschitz constant, obtained by the finite orthogonal direction cover. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LipschitzHilbert
open PacketRepresentation

def chartTruncation (d : Plane) (v : Plane → Plane) (epsilon R : ℝ)
    (f : SchwartzMap Plane ℂ) (x : Plane) : ℂ :=
  let z := planeCoordinates.symm (directionChart d x)
  productSymmetricTruncation
    (fun z => clippedChartSlope (chartField d v) (planeCoordinates z))
    (epsilon*chartDenominator (chartField d v) (planeCoordinates z))
    (R*chartDenominator (chartField d v) (planeCoordinates z)) (chartSchwartz d f) z

theorem chartTruncation_eq (d : Plane) (hd : ‖d‖=1) (v : Plane → Plane)
    (epsilon R : ℝ) (f : SchwartzMap Plane ℂ) (x : Plane) (hx : dist (v x) d<1/10) :
    chartTruncation d v epsilon R f x=shortTransform v epsilon R f x := by
  have hc := chart_coordinates hd hx
  have hfield : chartField d v (directionChart d x)=directionChart d (v x) := by
    simp only [chartField,LinearIsometryEquiv.symm_apply_apply]
  have h := shortTransform_clippedChart (chartField d v) (directionChart d x) epsilon R
    (f ∘ (directionChart d).symm) (by rw [hfield]; exact hc.1) (by rw [hfield]; exact hc.2)
  rw [shortTransform_chart] at h
  have hfun : (chartSchwartz d f : (ℝ×ℝ) → ℂ)=(f ∘ (directionChart d).symm) ∘ planeCoordinates := by
    funext z
    exact chartSchwartz_apply d f z
  simpa only [chartTruncation,MeasurableEquiv.apply_symm_apply,hfun] using h.symm

theorem chartTruncation_bound (C : ℝ)
    (hbound : ∀ epsilon R : ℝ, 0<epsilon → epsilon≤R → R≤1/10000 →
      ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
      ∀ (a : (ℝ×ℝ) → ℝ), Measurable a → (∀ z, 1/2≤a z) → (∀ z, a z≤1) →
      ∀ f : SchwartzMap (ℝ×ℝ) ℂ,
        MemLp (fun z => productSymmetricTruncation (fun z => field (planeCoordinates z))
          (epsilon*a z) (R*a z) f z) 2 planeMeasure ∧
        eLpNorm (fun z => productSymmetricTruncation (fun z => field (planeCoordinates z))
          (epsilon*a z) (R*a z) f z) 2 planeMeasure≤ENNReal.ofReal (C*‖f.toLp 2 planeMeasure‖))
    (d : Plane) (v : Plane → Plane) (hv : LipschitzWith (1/100) v)
    (hunit : ∀ x, ‖v x‖=1) (epsilon R : ℝ) (he : 0<epsilon)
    (heR : epsilon≤R) (hR : R≤1/10000) (f : SchwartzMap Plane ℂ) :
    MemLp (chartTruncation d v epsilon R f) 2 volume ∧
      eLpNorm (chartTruncation d v epsilon R f) 2 volume≤ENNReal.ofReal (C*‖f.toLp 2 volume‖) := by
  let w := chartField d v
  have hw : LipschitzWith (1/100) w := chartField_lipschitz d hv
  have hwu : ∀ x, ‖w x‖=1 := chartField_unit d hunit
  let a := fun z => chartDenominator w (planeCoordinates z)
  obtain ⟨hm, hb⟩ := hbound epsilon R he heR hR (clippedChartSlope w)
    (clippedChartSlope_small_lipschitz w hw hwu) (clippedChartSlope_abs w)
    a ((chartDenominator_measurable w hw).comp planeCoordinates.measurable)
    (fun z => (chartDenominator_bounds w hwu _).1)
    (fun z => (chartDenominator_bounds w hwu _).2) (chartSchwartz d f)
  have hmp := chartInverse_measurePreserving d
  refine ⟨hm.comp_measurePreserving hmp,?_⟩
  change eLpNorm ((fun z => productSymmetricTruncation
      (fun z => clippedChartSlope w (planeCoordinates z)) (epsilon*a z) (R*a z)
      (chartSchwartz d f) z) ∘ (fun x => planeCoordinates.symm (directionChart d x))) 2 volume≤_
  rw [eLpNorm_comp_measurePreserving hm.aestronglyMeasurable hmp]
  simpa only [planeMeasure,chartSchwartz_norm] using hb

theorem conditional_unit_small_lipschitz (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (hReassembly : BandToFullInput) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R : ℝ, 0<epsilon → epsilon≤R → R≤1/10000 →
    ∀ (v : Plane → Plane), LipschitzWith (1/100) v → (∀ x, ‖v x‖=1) →
    ∀ f : SchwartzMap Plane ℂ,
      eLpNorm (shortTransform v epsilon R f) 2 volume≤ENNReal.ofReal (C*‖f.toLp 2 volume‖) := by
  classical
  obtain ⟨C,hC,hbound⟩ := conditional_variable_slope_truncation hVariation hLL hH hReassembly
  obtain ⟨D,hDu,hDcover⟩ := exists_finite_direction_charts
  have hDne : D.Nonempty := by
    obtain ⟨d,hd,_⟩ := hDcover horizontalUnit horizontalUnit_norm
    exact ⟨d,hd⟩
  refine ⟨D.card*C,by positivity,?_⟩
  intro epsilon R he heR hR v hv hunit f
  have hb (d : Plane) := chartTruncation_bound C hbound d v hv hunit epsilon R he heR hR f
  have hcover (x : Plane) : ∃ d∈D, shortTransform v epsilon R f x=chartTruncation d v epsilon R f x := by
    obtain ⟨d,hd,hdist⟩ := hDcover (v x) (hunit x)
    exact ⟨d,hd,(chartTruncation_eq d (hDu d hd) v epsilon R f x hdist).symm⟩
  have hm : AEStronglyMeasurable (shortTransform v epsilon R f) volume :=
    (shortTransform_continuous hv.continuous f.continuous he heR).aestronglyMeasurable
  calc
    _ ≤ ∑ d∈D, eLpNorm (chartTruncation d v epsilon R f) 2 volume :=
      eLpNorm_le_sum_of_pointwise_choice volume D _ _ hm (fun d _ => (hb d).1.aestronglyMeasurable) hcover
    _ ≤ ∑ _d∈D, ENNReal.ofReal (C*‖f.toLp 2 volume‖) :=
      Finset.sum_le_sum (fun d _ => (hb d).2)
    _ = ENNReal.ofReal ((D.card*C)*‖f.toLp 2 volume‖) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end LipschitzHilbert

end

end OAI
