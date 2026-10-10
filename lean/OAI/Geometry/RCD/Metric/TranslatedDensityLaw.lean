import OAI.Geometry.RCD.Coordinates.NormalizedDensityLaw
import Mathlib.MeasureTheory.Group.Integral

namespace OAI

/-! # Translated Euclidean test densities induce translated probability laws -/

open Set Filter MeasureTheory
open scoped Topology ENNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates

theorem normalized_density_translation {n : ℕ} {a b : Euclidean n → ℝ}
    (ha : Measurable a) (hb : Measurable b)
    (hai : Integrable a volume) (hbi : Integrable b volume)
    (ha0 : ∀ x, 0≤a x) (hb0 : ∀ x, 0≤b x)
    (hap : 0<∫ x, a x) (hbp : 0<∫ x, b x)
    (h : Euclidean n) (he : ∀ x, b x=a (x-h)) :
    normalizedDensityLaw volume hbi hb0 hbp=
      (normalizedDensityLaw volume hai ha0 hap).map (fun x => x+h) := by
  have ht : Measurable (fun x : Euclidean n => x+h) := measurable_id.add_const h
  have hm : (∫ x, b x)=(∫ x, a x) := by
    simp_rw [he]
    exact integral_sub_right_eq_self a h
  apply (ProbabilityMeasure.toFiniteMeasure_isEmbedding _).injective
  apply FiniteMeasure.ext_of_forall_integral_eq
  intro φ
  change (∫ x, φ x ∂(normalizedDensityLaw volume hbi hb0 hbp : Measure (Euclidean n)))=
    ∫ x, φ x ∂((normalizedDensityLaw volume hai ha0 hap).map (fun x => x+h) : Measure (Euclidean n))
  rw [normalizedDensityLaw_integral volume hb,
    ProbabilityMeasure.toMeasure_map,
    integral_map ht.aemeasurable φ.continuous.aestronglyMeasurable,
    normalizedDensityLaw_integral volume ha,hm]
  congr 1
  calc (∫ x, b x*φ x) = ∫ x, b (x+h)*φ (x+h) :=
      (integral_add_right_eq_self (fun x => b x*φ x) h).symm
    _ = ∫ x, a x*φ (x+h) := by simp_rw [he,add_sub_cancel_right]

end RegularPointCoordinates

end

end OAI
