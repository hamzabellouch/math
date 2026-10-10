import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

namespace OAI

/-! A finite cover of output points permits summing operator bounds.
No disjointness or regularity of the choice of a covering index is needed. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert

theorem eLpNorm_le_sum_of_pointwise_choice {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset I) (F : X → ℂ) (G : I → X → ℂ)
    (hF : AEStronglyMeasurable F μ) (hG : ∀ i∈s, AEStronglyMeasurable (G i) μ)
    (hcover : ∀ x, ∃ i∈s, F x=G i x) :
    eLpNorm F 2 μ≤∑ i∈s, eLpNorm (G i) 2 μ := by
  have hp (x : X) : ‖F x‖≤‖∑ i∈s, ‖G i x‖‖ := by
    obtain ⟨i, hi, heq⟩ := hcover x
    rw [heq,Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg (G j x))]
    exact Finset.single_le_sum (fun j _ => norm_nonneg (G j x)) hi
  calc
    _ ≤ eLpNorm (∑ i∈s, fun x => ‖G i x‖) 2 μ :=
      eLpNorm_mono hF (by simpa only [Finset.sum_apply] using hp)
    _ ≤ ∑ i∈s, eLpNorm (fun x => ‖G i x‖) 2 μ := eLpNorm_sum_le (by norm_num)
    _ = _ := Finset.sum_congr rfl (fun i hi => eLpNorm_norm (G i) (hG i hi))

end LipschitzHilbert

end

end OAI
