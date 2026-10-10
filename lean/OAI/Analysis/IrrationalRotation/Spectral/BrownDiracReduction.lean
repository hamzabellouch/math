import OAI.Analysis.IrrationalRotation.Spectral.DeterminantHomogeneity
import OAI.Analysis.IrrationalRotation.Spectral.VectorSpectral

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233

section Algebra
variable {A : Type*} [CStarAlgebra A]

theorem sub_scalar_eq_neg_smul_normalized (a : A) (z : ℂ) (hz : z ≠ 0) :
    a - algebraMap ℂ A z = (-z) • (1 - z⁻¹ • a) := by
  rw [smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ hz]
  simp [Algebra.algebraMap_eq_smul_one, neg_smul, sub_eq_add_neg, add_comm]

theorem fugledeKadisonDeterminant_sub_scalar (τ : TracialState A)
    (a : A) (z : ℂ) (hz : z ≠ 0) :
    fugledeKadisonDeterminant τ (a - algebraMap ℂ A z) =
      ENNReal.ofReal ‖z‖ * fugledeKadisonDeterminant τ (1 - z⁻¹ • a) := by
  rw [sub_scalar_eq_neg_smul_normalized a z hz, fugledeKadisonDeterminant_smul,
    norm_neg]

theorem isBrownMeasure_dirac_zero_iff (τ : TracialState A) (a : A) :
    IsBrownMeasure τ a (Measure.dirac 0) ↔
      fugledeKadisonDeterminant τ a = 0 ∧
        ∀ z : ℂ, z ≠ 0 → fugledeKadisonDeterminant τ (1 - z⁻¹ • a) = 1 := by
  constructor
  · rintro ⟨_, _, h⟩
    constructor
    · simpa [logarithmicPotentialDeterminant_dirac] using h 0
    · intro z hz
      have hz' := h z
      rw [fugledeKadisonDeterminant_sub_scalar τ a z hz,
        logarithmicPotentialDeterminant_dirac] at hz'
      simp only [zero_sub, norm_neg] at hz'
      exact (ENNReal.mul_eq_left
        (ENNReal.ofReal_ne_zero_iff.mpr (norm_pos_iff.mpr hz))
        ENNReal.ofReal_ne_top).mp hz'
  · rintro ⟨hzero, hnormalized⟩
    refine ⟨inferInstance, ?_, ?_⟩
    · have hs : (Measure.dirac (0 : ℂ)).support ⊆ ({0} : Set ℂ) :=
        Measure.support_subset_of_isClosed isClosed_singleton (by simp)
      exact isCompact_singleton.of_isClosed_subset Measure.isClosed_support hs
    · intro z
      by_cases hz : z = 0
      · subst z
        simpa [logarithmicPotentialDeterminant_dirac] using hzero
      · rw [fugledeKadisonDeterminant_sub_scalar τ a z hz, hnormalized z hz,
          mul_one, logarithmicPotentialDeterminant_dirac]
        simp

end Algebra

section Vector
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem vectorFugledeKadisonDeterminant_sub_scalar (ξ : H) (hξ : ‖ξ‖ = 1)
    (T : H →L[ℂ] H) (z : ℂ) (hz : z ≠ 0) :
    vectorFugledeKadisonDeterminant ξ (T - z • (1 : H →L[ℂ] H)) =
      ENNReal.ofReal ‖z‖ * vectorFugledeKadisonDeterminant ξ (1 - z⁻¹ • T) := by
  rw [← Algebra.algebraMap_eq_smul_one,
    sub_scalar_eq_neg_smul_normalized T z hz,
    vectorFugledeKadisonDeterminant_smul ξ hξ, norm_neg]

theorem isVectorBrownMeasure_dirac_zero_iff (ξ : H) (hξ : ‖ξ‖ = 1)
    (T : H →L[ℂ] H) :
    IsVectorBrownMeasure ξ T (Measure.dirac 0) ↔
      vectorFugledeKadisonDeterminant ξ T = 0 ∧
        ∀ z : ℂ, z ≠ 0 → vectorFugledeKadisonDeterminant ξ (1 - z⁻¹ • T) = 1 := by
  constructor
  · rintro ⟨_, _, h⟩
    constructor
    · simpa [logarithmicPotentialDeterminant_dirac] using h 0
    · intro z hz
      have hz' := h z
      rw [vectorFugledeKadisonDeterminant_sub_scalar ξ hξ T z hz,
        logarithmicPotentialDeterminant_dirac] at hz'
      simp only [zero_sub, norm_neg] at hz'
      exact (ENNReal.mul_eq_left
        (ENNReal.ofReal_ne_zero_iff.mpr (norm_pos_iff.mpr hz))
        ENNReal.ofReal_ne_top).mp hz'
  · rintro ⟨hzero, hnormalized⟩
    refine ⟨inferInstance, ?_, ?_⟩
    · have hs : (Measure.dirac (0 : ℂ)).support ⊆ ({0} : Set ℂ) :=
        Measure.support_subset_of_isClosed isClosed_singleton (by simp)
      exact isCompact_singleton.of_isClosed_subset Measure.isClosed_support hs
    · intro z
      by_cases hz : z = 0
      · subst z
        simpa [logarithmicPotentialDeterminant_dirac] using hzero
      · rw [vectorFugledeKadisonDeterminant_sub_scalar ξ hξ T z hz,
          hnormalized z hz, mul_one, logarithmicPotentialDeterminant_dirac]
        simp

end Vector
end Invariant233

end

end OAI
