import Mathlib.MeasureTheory.Measure.OpenPos
import OAI.Geometry.NodalSets.Charts.SphereReferenceMeasureFinite

namespace OAI

namespace Yau.Target
open Manifold Set MeasureTheory
open scoped ENNReal
noncomputable section
local instance sphereReferenceMeasurePositiveLocal1 : MeasurableSpace Base := borel Base
local instance sphereReferenceMeasurePositiveLocal2 : BorelSpace Base := ⟨rfl⟩

lemma roundCoordMeasure_openPos :
    (volume.withDensity (fun x ↦ ENNReal.ofReal (roundCoordDensity x))).IsOpenPosMeasure := by
  apply Measure.AbsolutelyContinuous.isOpenPosMeasure
    (μ := (volume : Measure Yau.Jets.Coord))
  exact withDensity_absolutelyContinuous'
    roundCoordDensity_smooth.continuous.measurable.ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall (fun x ↦ (ENNReal.ofReal_pos.mpr (roundCoordDensity_pos x)).ne'))

lemma sphereReferenceMeasure_openPos : sphereReferenceMeasure.IsOpenPosMeasure := by
  constructor
  intro U hU hUne
  obtain ⟨p,hp⟩ := hUne
  rw [sphereReferenceMeasure_eq_chart p]
  simp only [roundChartDensity_coord_eq]
  rw [Measure.map_apply (sphereChartCoordMap_smooth p).continuous.measurable hU.measurableSet]
  let := roundCoordMeasure_openPos
  exact (hU.preimage (sphereChartCoordMap_smooth p).continuous).measure_ne_zero _
    ⟨0,by simpa only [mem_preimage,sphereChartCoordMap_zero] using hp⟩

def sphereWeightedPairing (rho u v : Base → ℝ) : ℝ :=
  ∫ p, rho p*u p*v p ∂sphereReferenceMeasure

lemma sphereWeightedPairing_integrable (rho u v : Base → ℝ)
    (hr : Continuous rho) (hu : Continuous u) (hv : Continuous v) :
    Integrable (fun p ↦ rho p*u p*v p) sphereReferenceMeasure :=
  sphereReferenceMeasure_integrable_continuous _ ((hr.mul hu).mul hv)

lemma sphereWeightedPairing_self_pos (rho u : Base → ℝ)
    (hr : Continuous rho) (hp : ∀ p, 0 < rho p) (hu : Continuous u) (hne : u ≠ 0) :
    0 < sphereWeightedPairing rho u u := by
  let := sphereReferenceMeasure_openPos
  obtain ⟨p,hp'⟩ : ∃ p, u p ≠ 0 := by
    by_contra h
    apply hne
    funext p
    simpa using not_exists.mp h p
  apply integral_pos_of_integrable_nonneg_nonzero ((hr.mul hu).mul hu)
    (sphereWeightedPairing_integrable rho u u hr hu hu)
  · intro q
    change 0 ≤ rho q*u q*u q
    nlinarith [sq_nonneg (u q),hp q]
  · have h : 0 < rho p*u p*u p := by nlinarith [sq_pos_of_ne_zero hp',hp p]
    exact h.ne'

lemma sphereWeightedPairing_symm (rho u v : Base → ℝ) :
    sphereWeightedPairing rho u v = sphereWeightedPairing rho v u := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p ↦ by ring)

lemma sphereWeightedPairing_smul_left (rho u v : Base → ℝ) (t : ℝ) :
    sphereWeightedPairing rho (t • u) v = t*sphereWeightedPairing rho u v := by
  unfold sphereWeightedPairing
  have he : (fun p ↦ rho p*(t • u) p*v p) = fun p ↦ t*(rho p*u p*v p) := by
    funext p
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  rw [he,integral_const_mul]

lemma sphereWeightedPairing_add_left (rho u v w : Base → ℝ)
    (hr : Continuous rho) (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) :
    sphereWeightedPairing rho (u+v) w = sphereWeightedPairing rho u w+sphereWeightedPairing rho v w := by
  unfold sphereWeightedPairing
  simp only [Pi.add_apply,mul_add,add_mul]
  exact integral_add (sphereWeightedPairing_integrable rho u w hr hu hw)
    (sphereWeightedPairing_integrable rho v w hr hv hw)

end
end Yau.Target

end OAI
