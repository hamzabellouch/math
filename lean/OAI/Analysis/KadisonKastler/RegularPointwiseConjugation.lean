import OAI.Analysis.KadisonKastler.RegularCoreRepresentation

namespace OAI

/-! # Pointwise antiunitaries on the regular Hilbert space

These concrete maps will provide the conjugation for the modular core.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def regularPointwiseConjugation (J : H ≃ₗᵢ⋆[ℂ] H) :
    RegularCoreHilbert H ≃ₗᵢ⋆[ℂ] RegularCoreHilbert H where
  toFun := J.toLinearIsometry.toContinuousLinearMap.compLp
  invFun := J.symm.toLinearIsometry.toContinuousLinearMap.compLp
  left_inv f := by
    apply Lp.ext
    filter_upwards [J.symm.toLinearIsometry.toContinuousLinearMap.coeFn_compLp
      (J.toLinearIsometry.toContinuousLinearMap.compLp f),
      J.toLinearIsometry.toContinuousLinearMap.coeFn_compLp f] with t hs hj
    rw [hs, hj]
    exact J.symm_apply_apply (f t)
  right_inv f := by
    apply Lp.ext
    filter_upwards [J.toLinearIsometry.toContinuousLinearMap.coeFn_compLp
      (J.symm.toLinearIsometry.toContinuousLinearMap.compLp f),
      J.symm.toLinearIsometry.toContinuousLinearMap.coeFn_compLp f] with t hj hs
    rw [hj, hs]
    exact J.apply_symm_apply (f t)
  map_add' := (J.toLinearIsometry.toContinuousLinearMap.compLpₗ 2
    (volume : Measure ℝ)).map_add
  map_smul' := (J.toLinearIsometry.toContinuousLinearMap.compLpₗ 2
    (volume : Measure ℝ)).map_smulₛₗ
  norm_map' f := by
    have he : ∀ᵐ t ∂(volume : Measure ℝ),
        ‖J.toLinearIsometry.toContinuousLinearMap.compLp f t‖ = ‖f t‖ := by
      filter_upwards [J.toLinearIsometry.toContinuousLinearMap.coeFn_compLp f] with t hj
      rw [hj]
      exact J.norm_map (f t)
    exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.le)))
      (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.ge)))

omit [CompleteSpace H] in
theorem regularPointwiseConjugation_apply_ae (J : H ≃ₗᵢ⋆[ℂ] H)
    (f : RegularCoreHilbert H) :
    regularPointwiseConjugation J f =ᵐ[volume] fun t => J (f t) :=
  J.toLinearIsometry.toContinuousLinearMap.coeFn_compLp f

omit [CompleteSpace H] in
theorem regularPointwiseConjugation_involutive (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) : Function.Involutive (regularPointwiseConjugation J) := by
  intro f
  apply Lp.ext
  filter_upwards [regularPointwiseConjugation_apply_ae J
    (regularPointwiseConjugation J f), regularPointwiseConjugation_apply_ae J f]
    with t houter hinner
  rw [houter, hinner, hJ]

end

end KadisonKastler

end OAI
