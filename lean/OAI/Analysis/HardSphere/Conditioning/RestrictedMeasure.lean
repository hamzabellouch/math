import Mathlib

namespace OAI

section

section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {X : Type*} [MeasurableSpace X]

def subtypeConditional (P : Measure X) (S : Set X) : Measure S :=
  (P S)⁻¹ • P.comap Subtype.val

lemma subtypeConditional_apply (P : Measure X) {S : Set X} (hS : MeasurableSet S) (A : Set S) :
    subtypeConditional P S A=(P S)⁻¹*P (Subtype.val '' A) := by
  rw [subtypeConditional,Measure.smul_apply,smul_eq_mul,comap_subtype_coe_apply hS]

lemma subtypeConditional_probability (P : Measure X) [IsFiniteMeasure P]
    {S : Set X} (hS : MeasurableSet S) (hP : P S≠0) : IsProbabilityMeasure (subtypeConditional P S) := by
  constructor
  rw [subtypeConditional_apply P hS]
  simp only [Set.image_univ,Subtype.range_coe]
  exact ENNReal.inv_mul_cancel hP (measure_ne_top _ _)

lemma subtypeConditional_map (P : Measure X) {S : Set X} (hS : MeasurableSet S) :
    (subtypeConditional P S).map (Subtype.val:S→X)=(P S)⁻¹ • P.restrict S := by
  rw [subtypeConditional,Measure.map_smul, map_comap_subtype_coe hS]
  exact measurable_subtype_coe.aemeasurable

lemma subtypeConditional_preimage (P : Measure X) {S : Set X} (hS : MeasurableSet S) (A : Set X) :
    subtypeConditional P S (Subtype.val ⁻¹' A)=(P S)⁻¹*P (A∩S) := by
  rw [subtypeConditional_apply P hS]
  have he : Subtype.val '' (Subtype.val ⁻¹' A : Set S) = A∩S := by
    ext x
    simp only [Set.mem_image,Set.mem_preimage,Set.mem_inter_iff]
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨hy,y.property⟩
    · rintro ⟨hx,hs⟩
      exact ⟨⟨x,hs⟩,hx,rfl⟩
  rw [he]

lemma subtypeConditional_le {S : Set X} (P : Measure X) (hS : MeasurableSet S)
    (A : Set X) {a b : ℝ≥0∞} (ha : a≤P S) (hb : P (A∩S)≤b) :
    subtypeConditional P S (Subtype.val ⁻¹' A)≤a⁻¹*b := by
  rw [subtypeConditional_preimage P hS]
  exact mul_le_mul' (ENNReal.inv_le_inv.mpr ha) hb

end HardSphere.Comparison

end
end

end

end OAI
