import OAI.Probability.InvariantIsing.Magnetic.MagneticHeightSupport

namespace OAI

/-! Constrained finite-field concavity on the strict height cone, derived
from the actual magnetic supporting planes. -/

noncomputable section
open Set
open scoped BigOperators

namespace InvariantIsing

theorem concaveOn_constrainedHeightFieldValue (h : FieldStep) {m : ℝ} (hm : |m| < 1) :
    ConcaveOn ℝ (fieldStrictHeightCone h.depth) (constrainedHeightFieldValue h m) := by
  refine ⟨convex_fieldStrictHeightCone _, ?_⟩
  intro r hr q hq a b ha hb hab
  let p := a • r + b • q
  have hp : p ∈ fieldStrictHeightCone h.depth :=
    convex_fieldStrictHeightCone _ hr hq ha hb hab
  let G := fun i : Fin (h.depth + 1) => -(h.cut i.succ - h.cut i.castSucc) / 2 *
    magneticFieldLevel (fieldStepOfStrictHeights h p hp) m i
  have hR := magneticHeight_support_strict h hm p r hp hr
  have hQ := magneticHeight_support_strict h hm p q hp hq
  change constrainedFieldValue (fieldStepOfStrictHeights h r hr) m ≤
    constrainedFieldValue (fieldStepOfStrictHeights h p hp) m +
      ∑ i, G i * (r i - p i) at hR
  change constrainedFieldValue (fieldStepOfStrictHeights h q hq) m ≤
    constrainedFieldValue (fieldStepOfStrictHeights h p hp) m +
      ∑ i, G i * (q i - p i) at hQ
  have hc : a * (∑ i, G i * (r i - p i)) +
      b * (∑ i, G i * (q i - p i)) = 0 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    have he : a * (r i - p i) + b * (q i - p i) = 0 := by
      calc
        _ = a * r i + b * q i - (a + b) * p i := by ring
        _ = 0 := by
          rw [hab, one_mul]
          simp only [p, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_self]
    calc
      a * (G i * (r i - p i)) + b * (G i * (q i - p i)) =
          G i * (a * (r i - p i) + b * (q i - p i)) := by ring
      _ = 0 := by rw [he, mul_zero]
  have hRa := mul_le_mul_of_nonneg_left hR ha
  have hQb := mul_le_mul_of_nonneg_left hQ hb
  have hv : a * constrainedFieldValue (fieldStepOfStrictHeights h p hp) m +
      b * constrainedFieldValue (fieldStepOfStrictHeights h p hp) m =
      constrainedFieldValue (fieldStepOfStrictHeights h p hp) m := by
    rw [← add_mul, hab, one_mul]
  change a * constrainedHeightFieldValue h m r + b * constrainedHeightFieldValue h m q ≤
    constrainedHeightFieldValue h m p
  simp only [constrainedHeightFieldValue, dite_eq_left hr, dite_eq_left hq, dite_eq_left hp]
  nlinarith [hRa, hQb, hc, hv]

end InvariantIsing

end

end OAI
