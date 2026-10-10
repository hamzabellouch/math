import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

namespace OAI

/-! # Incidence cost of direction-dependent exceptional slice parameters -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {Z X W : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace W]

theorem slice_direction_deletion_cost
    (ζ : Measure Z) (α : Z → Measure X) (β : Measure W)
    [SFinite ζ] [SFinite β] [∀ z, SFinite (α z)]
    (D : Set (Z × W)) (hD : MeasurableSet D) (E : Set (X × W))
    {P C : ℝ≥0∞} (hP : ∀ z, α z univ ≤ P)
    (hC : ∀ w, ζ {z | (z,w) ∈ D} ≤ C) :
    (∫⁻ z, ((α z).prod β) (E ∩ (univ ×ˢ {w | (z,w) ∈ D})) ∂ζ) ≤ P*C*β univ := by
  have hm : Measurable (fun z => β {w | (z,w) ∈ D}) := measurable_measure_prodMk_left hD
  calc
    _ ≤ ∫⁻ z, P*β {w | (z,w) ∈ D} ∂ζ := by
      apply lintegral_mono
      intro z
      calc
        _ ≤ ((α z).prod β) (univ ×ˢ {w | (z,w) ∈ D}) := measure_mono inter_subset_right
        _ = α z univ*β {w | (z,w) ∈ D} := by rw [Measure.prod_prod]
        _ ≤ _ := mul_le_mul_left (hP z) _
    _ = P*(ζ.prod β) D := by
      rw [lintegral_const_mul _ hm]
      exact congrArg (fun t => P*t) (Measure.prod_apply hD).symm
    _ ≤ P*(C*β univ) := by
      apply mul_le_mul_right
      rw [Measure.prod_apply_symm hD]
      exact (lintegral_mono hC).trans_eq (lintegral_const _)
    _ = _ := (mul_assoc _ _ _).symm

end Falconer

end OAI
