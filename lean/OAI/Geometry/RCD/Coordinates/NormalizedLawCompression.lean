import OAI.Geometry.RCD.Coordinates.NormalizedProbabilityLaw

namespace OAI

/-! # Exact measure and support of normalized finite laws -/

open Set MeasureTheory Filter
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] [Nonempty X]

theorem normalizedProbabilityLaw_measure (μ : Measure X) [IsFiniteMeasure μ] (hμ : μ≠0) :
    (normalizedProbabilityLaw μ : Measure X)=(μ univ)⁻¹ • μ := by
  let F : FiniteMeasure X := ⟨μ,inferInstance⟩
  have hF : F≠0 := by
    intro hh
    exact hμ (congrArg FiniteMeasure.toMeasure hh)
  change (F.normalize : Measure X)=(μ univ)⁻¹ • μ
  rw [F.toMeasure_normalize_eq_of_nonzero hF,← Measure.coe_nnreal_smul,
    ENNReal.coe_inv (F.mass_nonzero_iff.mpr hF),FiniteMeasure.ennreal_mass]
  rfl

theorem normalized_restriction_ae_mem (μ : Measure X) {U : Set X}
    (hU : MeasurableSet U) [IsFiniteMeasure (μ.restrict U)] (hμ : μ.restrict U≠0) :
    ∀ᵐ x ∂(normalizedProbabilityLaw (μ.restrict U) : Measure X), x∈U := by
  rw [normalizedProbabilityLaw_measure _ hμ]
  apply ae_iff.mpr
  change (((μ.restrict U) univ)⁻¹ • μ.restrict U) Uᶜ=0
  simp only [Measure.smul_apply,Measure.restrict_apply hU.compl,
    compl_inter_self,measure_empty,smul_zero]

end RegularPointCoordinates

end

end OAI
