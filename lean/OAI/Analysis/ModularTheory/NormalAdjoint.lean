import OAI.Analysis.ModularTheory.TomitaRegularizer
import OAI.Analysis.ModularTheory.WeightRightMultiplier

namespace OAI

/-! The adjoint of a normal-ordered core element, regularized by the
explicit Gaussian approximate identity. Its finite-weight vector is the
actual Tomita Fourier vector, with no tracial identity assumed. -/

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped Topology ENNReal

namespace WeakPureInfiniteness
open BoundedRecovery

lemma modularStarEnvelope (g : BoundedContinuousFunction ℝ ℂ)
    (hg : Integrable (fun ω : ℝ => ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω))) :
    Integrable (fun ω : ℝ => ‖star g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω)) := by
  simpa only [BoundedContinuousFunction.star_apply, norm_star] using hg

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : StandardModularData H)

lemma modularAdjoint_halfGraph (a : H →L[ℂ] H) (ha : a ∈ S.M) :
    (star a S.xi, S.J (a S.xi)) ∈ S.D.halfGraph := by
  simpa only [star_star] using S.core_halfGraph (star a) (star_mem ha)

def modularNormalAdjointRegularized (a : H →L[ℂ] H)
    (g : BoundedContinuousFunction ℝ ℂ) (n : ℕ) :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) :=
  star (modularLpRepresentation volume S.D a * modularTranslationCalculus g) *
    modularTranslationCalculus (modularFrequencyGaussian n)

lemma modularNormalAdjoint_mem (a : H →L[ℂ] H) (ha : a ∈ S.M)
    (g : BoundedContinuousFunction ℝ ℂ) :
    star (modularLpRepresentation volume S.D a * modularTranslationCalculus g) ∈
      modularCrossedProduct (volume : Measure ℝ) S :=
  star_mem (mul_mem (modularCrossedProduct_coeff volume S ⟨a, ha⟩)
    (modularTranslationCalculus_mem S g))

lemma modularNormalAdjointRegularized_mem (a : H →L[ℂ] H) (ha : a ∈ S.M)
    (g : BoundedContinuousFunction ℝ ℂ) (n : ℕ) :
    modularNormalAdjointRegularized S a g n ∈ modularCrossedProduct (volume : Measure ℝ) S :=
  mul_mem (modularNormalAdjoint_mem S a ha g) (modularTranslationCalculus_mem S _)

lemma modularNormalAdjointRegularized_finite (a : H →L[ℂ] H)
    (g : BoundedContinuousFunction ℝ ℂ) (n : ℕ) :
    modularCoreSquareWeight S (modularNormalAdjointRegularized S a g n) < ⊤ :=
  modularCoreSquareWeight_mul_finite S _
    (modularTranslationCalculus_finite S _ (modularFrequencyGaussian_integrable n)) _

lemma modularNormalAdjointRegularized_vector (a : H →L[ℂ] H) (ha : a ∈ S.M)
    (g : BoundedContinuousFunction ℝ ℂ)
    (hg : Integrable (fun ω : ℝ => ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω))) (n : ℕ) :
    modularWeightVector S (modularNormalAdjointRegularized S a g n)
      (modularNormalAdjointRegularized_mem S a ha g n)
      (modularNormalAdjointRegularized_finite S a g n) =
        𝓕⁻ (modularTomitaFourierVector S.D (modularAdjoint_halfGraph S a ha)
          (star g) (modularStarEnvelope g hg) n) := by
  change modularWeightVector S
    (star (modularLpRepresentation volume S.D a * modularTranslationCalculus g) *
      modularTranslationCalculus (modularFrequencyGaussian n)) _ _ = _
  rw [modularWeightVector_mul S _ (modularTranslationCalculus_mem S _)
    (modularTranslationCalculus_finite S _ (modularFrequencyGaussian_integrable n))
    _ (modularNormalAdjoint_mem S a ha g), modularFrequencyGaussian_weightVector]
  rw [star_mul, ← map_star, ← map_star]
  change modularTranslationCalculus (star g)
    (modularLpRepresentation volume S.D (star a)
      (modularScalarInclusion volume S (modularTomitaKernelVector n))) = _
  rw [modularCoefficient_kernelVector, modularTranslationCalculus_apply,
    modularTomitaTimeVector_fourier S.D (modularAdjoint_halfGraph S a ha)
      (star g) (modularStarEnvelope g hg)]

lemma modularNormalAdjointRegularized_vector_tendsto (a : H →L[ℂ] H) (ha : a ∈ S.M)
    (g : BoundedContinuousFunction ℝ ℂ)
    (hg : Integrable (fun ω : ℝ => ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω))) :
    Tendsto (fun n => modularWeightVector S (modularNormalAdjointRegularized S a g n)
      (modularNormalAdjointRegularized_mem S a ha g n)
      (modularNormalAdjointRegularized_finite S a g n)) atTop
        (𝓝 (𝓕⁻ (modularTomitaLimitVector (star g) (modularStarEnvelope g hg)
          (S.J (a S.xi))))) := by
  simp_rw [modularNormalAdjointRegularized_vector S a ha g hg]
  exact (Lp.fourierTransformₗᵢ ℝ H).symm.continuous.continuousAt.tendsto.comp
    (modularTomitaFourierVector_tendsto S.D (modularAdjoint_halfGraph S a ha)
      (star g) (modularStarEnvelope g hg))

end WeakPureInfiniteness

end

end OAI
