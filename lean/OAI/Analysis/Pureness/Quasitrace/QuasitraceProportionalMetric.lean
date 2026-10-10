import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientFunctor
import OAI.Analysis.Pureness.Quasitrace.PositiveQuasitraceScaling

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal
variable {D E : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]
variable (T : CuntzPureness.PositiveQuasitrace D) (U : CuntzPureness.PositiveQuasitrace E)
variable (φ : D →⋆ₙₐ[ℂ] E) (c : ℝ≥0)
variable (hφ : ∀ a, U (Positive.map φ a) = (c : ℝ)*T a)

include hφ in
lemma metricSize_map_proportional (x : D) :
    U.metricSize (φ x) = (c : ℝ)^((3:ℝ)⁻¹)*T.metricSize x := by
  have he : Positive.starMul (φ x) = Positive.map φ (Positive.starMul x) := by
    apply Subtype.ext
    change star (φ x)*φ x=φ (star x*x)
    rw [map_mul,map_star]
  simp only [metricSize,he,hφ]
  exact Real.mul_rpow c.2 (T.nonneg _)

include hφ in
lemma distance_map_proportional (x y : D) :
    U.distance (φ x) (φ y) = (c : ℝ)^((3:ℝ)⁻¹)*T.distance x y := by
  unfold distance
  rw [← map_sub,T.metricSize_map_proportional U φ c hφ]

include hφ in
lemma complexValue_map_proportional (x : D) :
    U.complexValue (φ x) = (c : ℂ)*T.complexValue x := by
  rw [U.complexValue_map (T.scale c) φ hφ,T.scale_complexValue]

include hφ in
lemma isMetricCauchy_map_proportional {u : ℕ → D} (hu : T.IsMetricCauchy u) :
    U.IsMetricCauchy (fun n => φ (u n)) := by
  simpa only [IsMetricCauchy,T.distance_map_proportional U φ c hφ,mul_zero] using
    hu.const_mul ((c : ℝ)^((3:ℝ)⁻¹))

include hφ in
lemma isMetricNull_map_proportional {u : ℕ → D} (hu : T.IsMetricNull u) :
    U.IsMetricNull (fun n => φ (u n)) := by
  simpa only [IsMetricNull,T.metricSize_map_proportional U φ c hφ,mul_zero] using
    hu.const_mul ((c : ℝ)^((3:ℝ)⁻¹))

include hφ in
lemma isMetricCauchy_map_proportional_iff (hc : 0 < c) (u : ℕ → D) :
    U.IsMetricCauchy (fun n => φ (u n)) ↔ T.IsMetricCauchy u := by
  have hk : (c : ℝ)^((3:ℝ)⁻¹) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  constructor
  · intro h
    have hh := h.const_mul (((c : ℝ)^((3:ℝ)⁻¹))⁻¹)
    simpa only [IsMetricCauchy,T.distance_map_proportional U φ c hφ,
      ← mul_assoc,inv_mul_cancel₀ hk,one_mul,mul_zero] using hh
  · exact T.isMetricCauchy_map_proportional U φ c hφ

include hφ in
lemma isMetricNull_map_proportional_iff (hc : 0 < c) (u : ℕ → D) :
    U.IsMetricNull (fun n => φ (u n)) ↔ T.IsMetricNull u := by
  have hk : (c : ℝ)^((3:ℝ)⁻¹) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  constructor
  · intro h
    have hh := h.const_mul (((c : ℝ)^((3:ℝ)⁻¹))⁻¹)
    simpa only [IsMetricNull,T.metricSize_map_proportional U φ c hφ,
      ← mul_assoc,inv_mul_cancel₀ hk,one_mul,mul_zero] using hh
  · exact T.isMetricNull_map_proportional U φ c hφ
end CuntzPureness.PositiveQuasitrace

end

end OAI
