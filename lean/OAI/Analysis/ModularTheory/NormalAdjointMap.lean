import OAI.Analysis.ModularTheory.WeightAdjointMap

namespace OAI

/-! Identification of the conjugate-linear norm isometry on normal-ordered
weight vectors. This gives a common linear formula for the limits of
regularized adjoints, so finite sums can be treated without a false
termwise norm argument. -/

noncomputable section
open MeasureTheory FourierTransform

namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : StandardModularData H)

lemma modularGauge_coefficient_scalar (a : H →L[ℂ] H)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    S.D.lpGauge volume 1 (modularLpRepresentation volume S.D a
      (modularScalarInclusion volume S f)) =
        (ContinuousLinearMap.toSpanSingleton ℂ (a S.xi)).compLpL 2 volume f := by
  apply Lp.ext
  filter_upwards [S.D.lpGauge_ae volume 1 (modularLpRepresentation volume S.D a
      (modularScalarInclusion volume S f)),
    modularLpRepresentation_ae volume S.D a (modularScalarInclusion volume S f),
    modularScalarInclusion_ae volume S f,
    (ContinuousLinearMap.toSpanSingleton ℂ (a S.xi)).coeFn_compLpL f]
    with t hG hA hS hC
  rw [hG, one_mul, hA, hS, map_smul, S.fixes_xi, map_smul, map_smul]
  rw [map_smul, ← mul_apply_eq_comp, S.D.unitary_mul_neg, one_apply_eq_self, hC]
  rfl

lemma modularNormalOrdered_mem (a : H →L[ℂ] H) (ha : a ∈ S.M)
    (g : BoundedContinuousFunction ℝ ℂ) :
    modularLpRepresentation volume S.D a * modularTranslationCalculus g ∈
      modularCrossedProduct (volume : Measure ℝ) S :=
  mul_mem (modularCrossedProduct_coeff volume S ⟨a, ha⟩) (modularTranslationCalculus_mem S g)

lemma modularNormalOrdered_finite (a : H →L[ℂ] H)
    (g : BoundedContinuousFunction ℝ ℂ)
    (hg : Integrable (fun ω : ℝ => ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω))) :
    modularCoreSquareWeight S
      (modularLpRepresentation volume S.D a * modularTranslationCalculus g) < ⊤ :=
  modularCoreSquareWeight_mul_finite S _ (modularTranslationCalculus_finite S g hg) _

lemma modularNormalWeightVector_gauge (a : H →L[ℂ] H) (ha : a ∈ S.M)
    (g : BoundedContinuousFunction ℝ ℂ)
    (hg : Integrable (fun ω : ℝ => ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω))) :
    S.D.lpGauge volume 1
      (modularWeightVector S
        (modularLpRepresentation volume S.D a * modularTranslationCalculus g)
        (modularNormalOrdered_mem S a ha g) (modularNormalOrdered_finite S a g hg)) =
      (ContinuousLinearMap.toSpanSingleton ℂ (a S.xi)).compLpL 2 volume
        (𝓕⁻ (modularWeightedVector g hg)) := by
  rw [modularWeightVector_mul S _ (modularTranslationCalculus_mem S g)
    (modularTranslationCalculus_finite S g hg) _
    (modularCrossedProduct_coeff volume S ⟨a, ha⟩),
    modularTranslationCalculus_weightVector S g hg]
  exact modularGauge_coefficient_scalar S a _

lemma modularConjugationLp_weightedCoefficient (a : H →L[ℂ] H)
    (g : BoundedContinuousFunction ℝ ℂ)
    (hg : Integrable (fun ω : ℝ => ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω))) :
    modularConjugationLp S
      ((ContinuousLinearMap.toSpanSingleton ℂ (a S.xi)).compLpL 2 volume
        (modularWeightedVector g hg)) =
      modularTomitaLimitVector (star g) (modularStarEnvelope g hg) (S.J (a S.xi)) := by
  apply Lp.ext
  filter_upwards [modularConjugationLp_ae S
      ((ContinuousLinearMap.toSpanSingleton ℂ (a S.xi)).compLpL 2 volume
        (modularWeightedVector g hg)),
    (ContinuousLinearMap.toSpanSingleton ℂ (a S.xi)).coeFn_compLpL
      (modularWeightedVector g hg), modularWeightedVector_ae g hg,
    modularTomitaLimitVector_ae (star g) (modularStarEnvelope g hg) (S.J (a S.xi))]
    with ω hJ hC hW hL
  rw [hJ, hC, hW, hL]
  change S.J (modularWeightedFunction g ω • a S.xi) = _
  rw [map_smulₛₗ]
  congr 1
  change (starRingEnd ℂ) (g ω * (Real.exp (Real.pi * ω) : ℂ)) =
    star (g ω) * (Real.exp (Real.pi * ω) : ℂ)
  rw [map_mul]
  congr 1
  exact Complex.conj_ofReal _

lemma modularWeightAdjointMap_normal (a : H →L[ℂ] H) (ha : a ∈ S.M)
    (g : BoundedContinuousFunction ℝ ℂ)
    (hg : Integrable (fun ω : ℝ => ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω))) :
    modularWeightAdjointMap S
      (modularWeightVector S
        (modularLpRepresentation volume S.D a * modularTranslationCalculus g)
        (modularNormalOrdered_mem S a ha g) (modularNormalOrdered_finite S a g hg)) =
      𝓕⁻ (modularTomitaLimitVector (star g) (modularStarEnvelope g hg) (S.J (a S.xi))) := by
  unfold modularWeightAdjointMap
  rw [modularNormalWeightVector_gauge S a ha g hg, fourier_compLp,
    fourier_fourierInv_eq, modularConjugationLp_weightedCoefficient]

end WeakPureInfiniteness

end

end OAI
