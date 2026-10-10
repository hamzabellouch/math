import OAI.Analysis.IrrationalRotation.Spectral.DeterminantSemicontinuity
import OAI.Analysis.IrrationalRotation.Spectral.DeterminantContinuity
import OAI.Analysis.IrrationalRotation.Analysis.ExponentialDecay
import OAI.Analysis.IrrationalRotation.Spectral.RotationDeterminant
import OAI.Analysis.IrrationalRotation.Spectral.ProductSpectralBundle

namespace OAI

noncomputable section
open scoped ENNReal

namespace Invariant233

section CStar
variable {A : Type*} [CStarAlgebra A]

theorem continuous_fugledeKadisonDeterminant_sub_scalar_of_spectrum_subset_zero
    (τ : TracialState A) (a : A) (hσ : spectrum ℂ a ⊆ {0})
    (hzero : fugledeKadisonDeterminant τ a = 0) :
    Continuous (fun z : ℂ => fugledeKadisonDeterminant τ (a - algebraMap ℂ A z)) := by
  rw [continuous_iff_continuousAt]
  intro z
  have hc : ContinuousAt (fugledeKadisonDeterminant τ) (a - algebraMap ℂ A z) := by
    by_cases hz : z = 0
    · subst z
      simpa using continuousAt_fugledeKadisonDeterminant_of_eq_zero τ hzero
    · apply continuousAt_fugledeKadisonDeterminant_of_isUnit
      have hnot : z ∉ spectrum ℂ a := fun h => hz (hσ h)
      simpa only [neg_sub] using (spectrum.notMem_iff.mp hnot).neg
  exact ContinuousAt.comp (f := fun w : ℂ => a - algebraMap ℂ A w) hc (by fun_prop)

theorem continuous_fugledeKadisonDeterminant_sub_scalar_of_normQuasinilpotent
    (τ : TracialState A) (a : A) (ha : NormQuasinilpotent a)
    (hzero : fugledeKadisonDeterminant τ a = 0) :
    Continuous (fun z : ℂ => fugledeKadisonDeterminant τ (a - algebraMap ℂ A z)) :=
  continuous_fugledeKadisonDeterminant_sub_scalar_of_spectrum_subset_zero τ a
    (spectrum_subset_zero_of_spectralRadius_zero a
      (spectralRadius_eq_zero_of_normRoot_tendsto ha)) hzero

end CStar

section Vector
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem continuous_vectorFugledeKadisonDeterminant_sub_scalar_of_spectrum_subset_zero
    (ξ : H) (T : H →L[ℂ] H) (hσ : spectrum ℂ T ⊆ {0})
    (hzero : vectorFugledeKadisonDeterminant ξ T = 0) :
    Continuous (fun z : ℂ => vectorFugledeKadisonDeterminant ξ
      (T - z • (1 : H →L[ℂ] H))) := by
  rw [continuous_iff_continuousAt]
  intro z
  have hc : ContinuousAt (vectorFugledeKadisonDeterminant ξ)
      (T - z • (1 : H →L[ℂ] H)) := by
    by_cases hz : z = 0
    · subst z
      simpa using continuousAt_vectorFugledeKadisonDeterminant_of_eq_zero ξ hzero
    · apply continuousAt_vectorFugledeKadisonDeterminant_of_isUnit
      have hnot : z ∉ spectrum ℂ T := fun h => hz (hσ h)
      simpa only [neg_sub, Algebra.algebraMap_eq_smul_one] using
        (spectrum.notMem_iff.mp hnot).neg
  exact ContinuousAt.comp (f := fun w : ℂ => T - w • (1 : H →L[ℂ] H)) hc (by fun_prop)

theorem continuous_vectorFugledeKadisonDeterminant_sub_scalar_of_normQuasinilpotent
    (ξ : H) (T : H →L[ℂ] H) (hT : NormQuasinilpotent T)
    (hzero : vectorFugledeKadisonDeterminant ξ T = 0) :
    Continuous (fun z : ℂ => vectorFugledeKadisonDeterminant ξ
      (T - z • (1 : H →L[ℂ] H))) :=
  continuous_vectorFugledeKadisonDeterminant_sub_scalar_of_spectrum_subset_zero ξ T
    (spectrum_subset_zero_of_spectralRadius_zero T
      (spectralRadius_eq_zero_of_normRoot_tendsto hT)) hzero

end Vector

namespace Rotation

theorem continuous_weight_spectralDeterminant (θ : ℝ) (hθ : Irrational θ)
    (f : C(Circle, ℝ)) (hf : IsContinuousCircleWeight f) :
    Continuous (fun z : ℂ => vectorFugledeKadisonDeterminant vacuum
      (weightedReal θ f - z • (1 : Hilbert →L[ℂ] Hilbert))) := by
  obtain ⟨_, hqn, hdet⟩ := continuous_weight_spectral_bundle θ hθ f hf
  exact continuous_vectorFugledeKadisonDeterminant_sub_scalar_of_normQuasinilpotent
    vacuum (weightedReal θ f) hqn hdet

end Rotation

namespace ProductModel

theorem continuous_weightedOperator_spectralDeterminant
    (θ c : ℕ → ℝ) (hθ01 : ∀ i, θ i ∈ Set.Ico (0 : ℝ) 1)
    (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (hlog : HasNegInfiniteLogIntegral baseMeasure (weight θ c)) :
    Continuous (fun z : ℂ => vectorFugledeKadisonDeterminant traceVector
      (weightedOperator θ c - z • (1 : Hilbert →L[ℂ] Hilbert))) :=
  continuous_vectorFugledeKadisonDeterminant_sub_scalar_of_normQuasinilpotent
    traceVector (weightedOperator θ c)
    (weightedOperator_normQuasinilpotent_of_logIntegral θ c hθ01 hc hθ hlog)
    (weightedOperator_vectorDeterminant_zero θ c (fun i => (hθ01 i).1) hc hθ hlog)

end ProductModel
end Invariant233

end

end OAI
