import OAI.Analysis.IrrationalRotation.Model.Rotation

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.Rotation

def measurableOrbitWeight (θ : ℝ) (g : Circle → ℂ) (C : ℝ)
    (hb : ∀ x, ‖g x‖ ≤ C) (x : Circle) : WeightedShift.Weight :=
  ⟨fun k => g (action θ k x), memℓp_infty <| by
    refine ⟨C, ?_⟩
    rintro r ⟨k, rfl⟩
    exact hb _⟩

def measurableRepresentation (θ : ℝ) (g : Circle → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) : Hilbert →L[ℂ] Hilbert :=
  WeightedShift.fieldDiagonal (measurableOrbitWeight θ g C hb) C hC
    (fun _ => lp.norm_le_of_forall_le hC (fun _ => hb _))
    (fun _k => (hg.comp (continuous_id.add continuous_const).measurable).aestronglyMeasurable)

end Invariant233.Rotation

end

end OAI
