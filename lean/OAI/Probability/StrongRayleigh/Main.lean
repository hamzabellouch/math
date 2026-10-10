import OAI.Probability.StrongRayleigh.Model
import OAI.Probability.StrongRayleigh.RayleighResponse
import OAI.Probability.StrongRayleigh.FiniteDPPExistence
import OAI.Probability.StrongRayleigh.FiniteDPPStability
import OAI.Probability.StrongRayleigh.CountableAssembly
import OAI.Probability.StrongRayleigh.MarginalBridge
import OAI.Probability.StrongRayleigh.TranslationAssembly
import OAI.Probability.StrongRayleigh.GroupFactorProof

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Topology ComplexConjugate

namespace Problem336AdditiveD139

theorem finite_strongly_rayleigh_response :
    ∀ (F : Type u_1) [Fintype F] [Nonempty F] (μ : ProbabilityMeasure (F → Bool)),
      StronglyRayleighFinite μ →
        (∀ (i j : F) (h : F → ℝ),
          HasDerivAt (fun r : ℝ => tiltMean μ (coordinatePerturb h j r) i)
            (tiltCovariance μ h i j) 0) ∧
        (∀ (i : F) (h : F → ℝ),
          (∑ j : F, |tiltCovariance μ h i j|) ≤
              2 * tiltMean μ h i * (1 - tiltMean μ h i) ∧
            2 * tiltMean μ h i * (1 - tiltMean μ h i) ≤ (1 : ℝ) / 2) ∧
        (∀ (i : F) (h h' : F → ℝ) (D : ℝ),
          0 ≤ D → (∀ j : F, |h j - h' j| ≤ D) →
            |tiltMean μ h i - tiltMean μ h' i| ≤ D / 2) := by
  intro F _ _ μ hμ
  exact finite_response_of_covariance_signs μ
    (fun i j h hij => hμ.tiltCovariance_nonpos h i j hij)
    (fun i h => hμ.tiltCovariance_row_nonneg h i)

theorem strongly_rayleigh_group_factor :
    ∀ (Γ : Type u_2) [Group Γ] [Countable Γ] [MeasurableSpace Γ],
      ∀ μ : ProbabilityMeasure (Γ → Bool),
        StronglyRayleighCountable μ → InvariantBinaryLaw μ → HasEquivariantIIDFactor μ := by
  intro Γ _ _ _ μ hSR hInv
  exact group_factor_of_finite_response
    (fun F _ _ ν hν => (finite_strongly_rayleigh_response F ν hν).2.2)
    μ hSR hInv

theorem finite_positive_contraction_dpp_is_strongly_rayleigh :
    ∀ (F : Type u_3) [Fintype F] [Nonempty F] (K : F → F → ℂ),
      PositiveContractionFinite K →
        (∃ μ : ProbabilityMeasure (F → Bool), IsFiniteDeterminantalLaw μ K) ∧
          ∀ μ : ProbabilityMeasure (F → Bool), IsFiniteDeterminantalLaw μ K →
            StronglyRayleighFinite μ := by
  intro F _ _ K hK
  exact ⟨hK.exists_finiteDPP, fun μ hμ => hμ.stronglyRayleighFinite hK⟩

theorem countable_positive_contraction_dpp_exists_unique :
    ∀ (I : Type u_4) [Countable I] (K : I → I → ℂ),
      PositiveContractionKernel K →
        ∃! μ : ProbabilityMeasure (I → Bool), IsDeterminantalLaw μ K := by
  intro I _ K hK
  exact positiveContractionKernel_existsUnique_of_finite_exists
    (fun F _ _ K hK => hK.exists_finiteDPP) I K hK

theorem invariant_positive_contraction_dpp_factor :
    ∀ (Γ : Type u_5) [Group Γ] [Countable Γ] [MeasurableSpace Γ]
      (K : Γ → Γ → ℂ) (μ : ProbabilityMeasure (Γ → Bool)),
      PositiveContractionKernel K → IsDeterminantalLaw μ K →
        InvariantBinaryLaw μ → HasEquivariantIIDFactor μ := by
  intro Γ _ _ _ K μ hK hμ hinv
  apply strongly_rayleigh_group_factor Γ μ ?_ hinv
  exact isDeterminantalLaw_stronglyRayleighCountable_of_finite K μ
    (fun F _ _ L hL ν hν => hν.stronglyRayleighFinite hL) hK hμ

theorem translation_invariant_kernel_dpp_factor :
    ∀ (Γ : Type u_6) [Group Γ] [Countable Γ] [MeasurableSpace Γ] (K : Γ → Γ → ℂ),
      PositiveContractionKernel K → TranslationInvariantKernel K →
        ∃ μ : ProbabilityMeasure (Γ → Bool),
          IsDeterminantalLaw μ K ∧ InvariantBinaryLaw μ ∧ HasEquivariantIIDFactor μ := by
  intro Γ _ _ _ K hK htranslation
  apply translationInvariantKernel_factor_of_exists K htranslation
    (countable_positive_contraction_dpp_exists_unique Γ K hK).exists
  intro μ hμ hinvariant
  exact invariant_positive_contraction_dpp_factor Γ K μ hK hμ hinvariant

end Problem336AdditiveD139

end

end OAI
