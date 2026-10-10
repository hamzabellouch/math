import OAI.Geometry.RCD.Coordinates.NormalizedLocalL1Domination

namespace OAI

/-! # Restricting a normalized compression bound to its actual support -/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem normalized_supported_compression (μ ν : Measure X) {S : Set X} {B : ℝ≥0∞} {C : ℝ}
    (hB : B≠∞) (hν : ν≤B • μ) (hs : ∀ᵐ x ∂ν, x∈S)
    (hV : 0<μ.real S) (hC : B.toReal*μ.real S≤C) :
    ν≤ENNReal.ofReal (C/μ.real S) • μ.restrict S := by
  have hcoef : B≤ENNReal.ofReal (C/μ.real S) := by
    rw [← ENNReal.ofReal_toReal hB]
    exact ENNReal.ofReal_le_ofReal ((le_div_iff₀ hV).mpr hC)
  calc
    ν=ν.restrict S := (Measure.restrict_eq_self_of_ae_mem hs).symm
    _ ≤ (B • μ).restrict S := Measure.restrict_mono_measure hν S
    _ = B • μ.restrict S := Measure.restrict_smul _ _ _
    _ ≤ _ := by
      apply Measure.le_iff.mpr
      intro U _hU
      simpa only [Measure.smul_apply,smul_eq_mul] using mul_le_mul' hcoef (le_refl (μ.restrict S U))

end RegularPointCoordinates

end

end OAI
