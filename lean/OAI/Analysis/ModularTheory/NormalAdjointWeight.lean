import OAI.Analysis.ModularTheory.NormalAdjoint

namespace OAI

/-! Adjoint-weight symmetry for a normal-ordered core element. Both bounds
come from actual Gaussian regularizations: closedness gives one direction,
and right-multiplier contractivity gives the reverse direction. -/

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped Topology ENNReal

namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : StandardModularData H)

lemma modularNormalOrdered_adjoint_weight (a : H →L[ℂ] H) (ha : a ∈ S.M)
    (g : BoundedContinuousFunction ℝ ℂ)
    (hg : Integrable (fun ω : ℝ => ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω))) :
    modularCoreSquareWeight S
        (star (modularLpRepresentation volume S.D a * modularTranslationCalculus g)) =
      modularCoreSquareWeight S
        (modularLpRepresentation volume S.D a * modularTranslationCalculus g) := by
  let R := modularNormalAdjointRegularized S a g
  let ζ : Lp H 2 (volume : Measure ℝ) :=
    𝓕⁻ (modularTomitaLimitVector (star g) (modularStarEnvelope g hg) (S.J (a S.xi)))
  let C : ℝ := ‖a S.xi‖ ^ 2 * ∫ ω : ℝ, ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω)
  have hζ : ‖ζ‖ ^ 2 = C := by
    change ‖(Lp.fourierTransformₗᵢ ℝ H).symm
      (modularTomitaLimitVector (star g) (modularStarEnvelope g hg) (S.J (a S.xi)))‖ ^ 2 = _
    rw [(Lp.fourierTransformₗᵢ ℝ H).symm.norm_map, modularTomitaLimitVector_norm_sq,
      S.J.norm_map]
    simp only [C, BoundedContinuousFunction.star_apply, norm_star]
  have hlim : Tendsto (fun n => modularWeightVector S (R n)
      (modularNormalAdjointRegularized_mem S a ha g n)
      (modularNormalAdjointRegularized_finite S a g n)) atTop (𝓝 ζ) :=
    modularNormalAdjointRegularized_vector_tendsto S a ha g hg
  let T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) :=
    star (modularLpRepresentation volume S.D a * modularTranslationCalculus g)
  have hstrong : ∀ f : Lp H 2 (volume : Measure ℝ),
      Tendsto (fun n => R n f) atTop (𝓝 (T f)) := by
    intro f
    exact T.continuous.continuousAt.tendsto.comp (modularFrequencyGaussian_strong f)
  have hle := modularCoreSquareWeight_le_of_strong_weightVectors S R
    (modularNormalAdjointRegularized_mem S a ha g)
    (modularNormalAdjointRegularized_finite S a g) _ hstrong ζ hlim
  rw [hζ] at hle
  have hge : ENNReal.ofReal C ≤ modularCoreSquareWeight S
      (star (modularLpRepresentation volume S.D a * modularTranslationCalculus g)) := by
    have hn := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hlim.norm).pow 2)
    simp only [Function.comp_def, hζ] at hn
    apply le_of_tendsto hn
    apply Eventually.of_forall
    intro n
    rw [modularWeightVector_norm_sq, ENNReal.ofReal_toReal
      (modularNormalAdjointRegularized_finite S a g n).ne]
    exact modularCoreSquareWeight_rightMultiplier S _ (modularNormalAdjoint_mem S a ha g)
      (modularFrequencyGaussian n)
      ((BoundedContinuousFunction.norm_le zero_le_one).mpr (modularFrequencyGaussian_norm n))
  have hfin : modularCoreSquareWeight S
      (modularLpRepresentation volume S.D a * modularTranslationCalculus g) < ⊤ :=
    modularCoreSquareWeight_mul_finite S _ (modularTranslationCalculus_finite S g hg) _
  have hnormal : modularCoreSquareWeight S
      (modularLpRepresentation volume S.D a * modularTranslationCalculus g) = ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_toReal hfin.ne]
    congr 1
    exact modularNormalOrdered_weight_exact S ⟨a, ha⟩ g hg
  rw [hnormal]
  exact le_antisymm hle hge

end WeakPureInfiniteness

end

end OAI
