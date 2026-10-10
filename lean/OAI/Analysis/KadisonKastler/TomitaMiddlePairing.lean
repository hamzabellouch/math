import OAI.Analysis.KadisonKastler.TomitaMiddleCore

namespace OAI

/-! # Symmetric pairings for the bounded conjugate-linear middle operator -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem tomitaPolarConjugation_inner_swap (v w : H) :
    inner ℂ (tomitaPolarConjugation J Ω hsep hcyc v) w =
      inner ℂ (tomitaPolarConjugation J Ω hsep hcyc w) v := by
  have h := conjugateIsometry_inner (tomitaPolarConjugation J Ω hsep hcyc)
    v (tomitaPolarConjugation J Ω hsep hcyc w)
  rw [tomitaPolarConjugation_involutive J Ω hsep hcyc] at h
  change inner ℂ (tomitaPolarConjugation J Ω hsep hcyc v) w =
    (starRingEnd ℂ) (inner ℂ v (tomitaPolarConjugation J Ω hsep hcyc w)) at h
  rwa [inner_conj_symm] at h

theorem tomitaMiddleOperator_inner_swap (v w : H) :
    inner ℂ (tomitaMiddleOperator (M := M) J Ω
      (tomitaPolarConjugation J Ω hsep hcyc v)) w =
    inner ℂ (tomitaMiddleOperator (M := M) J Ω
      (tomitaPolarConjugation J Ω hsep hcyc w)) v := by
  rw [tomitaMiddleOperator_polar J Ω hsep hcyc,
    tomitaPolarConjugation_inner_swap J Ω hsep hcyc]
  rw [← ContinuousLinearMap.adjoint_inner_left]
  have hs : (tomitaMiddleOperator (M := M) J Ω).adjoint =
      tomitaMiddleOperator (M := M) J Ω := (tomitaMiddleOperator_selfAdjoint J Ω).star_eq
  rw [hs]

end

end KadisonKastler

end OAI
