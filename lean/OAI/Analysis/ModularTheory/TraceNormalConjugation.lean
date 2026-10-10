import OAI.Analysis.ModularTheory.TracialRightAction
import OAI.Analysis.ModularTheory.NormalAdjointMap

namespace OAI

/-! The actual tracial conjugation agrees with the explicit Fourier formula
on normal-ordered finite-weight vectors. The identification uses two limits
of the same Gaussian-regularized adjoint. -/
noncomputable section
open MeasureTheory Filter FourierTransform
open scoped Topology
namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma modularTracialRightGaussian_strong (S : StandardModularData H)
    (x : Lp H 2 (volume : Measure ℝ)) :
    Tendsto (fun n => modularTracialRightAction S
      (modularTranslationCalculus (modularFrequencyGaussian n)) x) atTop (𝓝 x) := by
  have hs (n : ℕ) : star (modularFrequencyGaussian n) = modularFrequencyGaussian n := by
    ext ω
    change star (Real.exp (-(2 * Real.pi * ω) ^ 2 / (n + 1)) : ℂ) = _
    exact Complex.conj_ofReal _
  change Tendsto (fun n => modularTraceConjugation S
    (star (modularTranslationCalculus (modularFrequencyGaussian n))
      (modularTraceConjugation S x))) atTop (𝓝 x)
  simp only [← map_star, hs]
  simpa only [Function.comp_def, modularTraceConjugation_involutive S x] using
    (modularTraceConjugation S).continuous.continuousAt.tendsto.comp
      (modularFrequencyGaussian_strong (modularTraceConjugation S x))

lemma modularTraceConjugation_normal (S : StandardModularData H)
    (a : H →L[ℂ] H) (ha : a ∈ S.M) (g : BoundedContinuousFunction ℝ ℂ)
    (hg : Integrable (fun ω : ℝ => ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω))) :
    modularTraceConjugation S
      (modularWeightVector S
        (modularLpRepresentation volume S.D a * modularTranslationCalculus g)
        (modularNormalOrdered_mem S a ha g) (modularNormalOrdered_finite S a g hg)) =
      modularWeightAdjointMap S
        (modularWeightVector S
          (modularLpRepresentation volume S.D a * modularTranslationCalculus g)
          (modularNormalOrdered_mem S a ha g) (modularNormalOrdered_finite S a g hg)) := by
  let T : modularFiniteWeightSpace S :=
    ⟨modularLpRepresentation volume S.D a * modularTranslationCalculus g,
      modularNormalOrdered_mem S a ha g, modularNormalOrdered_finite S a g hg⟩
  let R (n : ℕ) := modularFiniteWeightRight S (modularFiniteWeightStar S T)
    (modularTranslationCalculus (modularFrequencyGaussian n))
    (modularTranslationCalculus_mem S _)
  have hlim : Tendsto (fun n => modularFiniteWeightMap S (R n)) atTop
      (𝓝 (modularFiniteWeightMap S (modularFiniteWeightStar S T))) := by
    have h := modularTracialRightGaussian_strong S
      (modularFiniteWeightMap S (modularFiniteWeightStar S T))
    have he (n : ℕ) : modularTracialRightAction S
        (modularTranslationCalculus (modularFrequencyGaussian n))
        (modularFiniteWeightMap S (modularFiniteWeightStar S T)) =
        modularFiniteWeightMap S (R n) :=
      modularTracialRightAction_vector S _ _ (modularTranslationCalculus_mem S _)
    exact h.congr' (Eventually.of_forall he)
  have hformula : Tendsto (fun n => modularFiniteWeightMap S (R n)) atTop
      (𝓝 (modularWeightAdjointMap S (modularFiniteWeightMap S T))) := by
    change Tendsto (fun n => modularWeightVector S
      (modularNormalAdjointRegularized S a g n)
      (modularNormalAdjointRegularized_mem S a ha g n)
      (modularNormalAdjointRegularized_finite S a g n)) atTop
      (𝓝 (modularWeightAdjointMap S (modularWeightVector S
        (modularLpRepresentation volume S.D a * modularTranslationCalculus g)
        (modularNormalOrdered_mem S a ha g) (modularNormalOrdered_finite S a g hg))))
    rw [modularWeightAdjointMap_normal S a ha g hg]
    exact modularNormalAdjointRegularized_vector_tendsto S a ha g hg
  change modularTraceConjugation S (modularFiniteWeightMap S T) = _
  rw [modularTraceConjugation_vector]
  exact tendsto_nhds_unique hlim hformula

end WeakPureInfiniteness

end

end OAI
