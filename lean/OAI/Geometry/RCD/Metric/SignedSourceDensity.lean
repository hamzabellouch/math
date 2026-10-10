import OAI.Geometry.RCD.Coordinates.WeightedBilinearMeasure
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

namespace OAI

/-! # Integrating a full signed source and an integrable density -/

open Set MeasureTheory
open scoped BoundedContinuousFunction ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A bounded continuous test integrates an integrable signed density by
the expected product formula, without discarding either sign. -/
theorem integral_signedDensity (μ : Measure X) {f : X → ℝ} (hf : Integrable f μ)
    (w : X →ᵇ ℝ) :
    (∫ᵛ x, w x ∂<•(μ.withDensityᵥ f)) = ∫ x, w x * f x ∂μ := by
  let μp := μ.withDensity (fun x => ENNReal.ofReal (f x))
  let μn := μ.withDensity (fun x => ENNReal.ofReal (-f x))
  let : IsFiniteMeasure μp := isFiniteMeasure_withDensity_ofReal hf.2
  let : IsFiniteMeasure μn := isFiniteMeasure_withDensity_ofReal hf.neg.2
  have hwp := PositiveBilinearMeasure.integrable_weight w μp.toSignedMeasure
  have hwn := PositiveBilinearMeasure.integrable_weight w μn.toSignedMeasure
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hf,
    VectorMeasure.integral_sub_vectorMeasure hwp hwn,
    VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure]
  change (∫ x, w x ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) -
    (∫ x, w x ∂μ.withDensity (fun x => ENNReal.ofReal ((-f) x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul₀
      hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul₀
      hf.neg.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hpos : Integrable (fun x => max (f x) 0 * w x) μ := by
    exact hf.pos_part.mul_bdd w.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall w.norm_coe_le_norm)
  have hneg : Integrable (fun x => max (-f x) 0 * w x) μ := by
    exact hf.neg.pos_part.mul_bdd w.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall w.norm_coe_le_norm)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal', Pi.neg_apply]
  rw [← integral_sub hpos hneg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    by_cases hx : 0 ≤ f x
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
      ring
    · rw [max_eq_right (le_of_not_ge hx), max_eq_left (le_of_lt (neg_pos.mpr (lt_of_not_ge hx)))]
      ring

end RegularPointCoordinates

end

end OAI
