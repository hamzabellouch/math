import OAI.Analysis.IrrationalRotation.Analysis.UnitaryTransport
import OAI.Analysis.IrrationalRotation.Spectral.VectorSpectral

namespace OAI

noncomputable section

namespace Invariant233

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace E] [CompleteSpace F]

theorem vectorTrace_conj (e : E ≃ₗᵢ[ℂ] F) (ξ : E) (A : E →L[ℂ] E) :
    vectorTrace (e ξ) (e.conjStarAlgEquiv A) = vectorTrace ξ A := by
  change inner ℂ (e ξ) (e (A (e.symm (e ξ)))) = inner ℂ ξ (A ξ)
  rw [e.symm_apply_apply]
  exact e.inner_map_map ξ (A ξ)

theorem vectorFugledeKadisonDeterminant_map
    (φ : (E →L[ℂ] E) →⋆ₐ[ℂ] (F →L[ℂ] F)) (ξ : E) (η : F)
    (hτ : ∀ A, vectorTrace η (φ A) = vectorTrace ξ A) (A : E →L[ℂ] E) :
    vectorFugledeKadisonDeterminant η (φ A) = vectorFugledeKadisonDeterminant ξ A := by
  unfold vectorFugledeKadisonDeterminant
  apply iInf_congr
  intro ε
  rw [← regularizedLog_map φ A ε.val ε.property, hτ]

theorem vectorFugledeKadisonDeterminant_conj
    (e : E ≃ₗᵢ[ℂ] F) (ξ : E) (A : E →L[ℂ] E) :
    vectorFugledeKadisonDeterminant (e ξ) (e.conjStarAlgEquiv A) =
      vectorFugledeKadisonDeterminant ξ A :=
  vectorFugledeKadisonDeterminant_map e.conjStarAlgEquiv.toStarAlgHom ξ (e ξ)
    (vectorTrace_conj e ξ) A

theorem isVectorBrownMeasure_conj_iff
    (e : E ≃ₗᵢ[ℂ] F) (ξ : E) (A : E →L[ℂ] E)
    (μ : MeasureTheory.Measure ℂ) :
    IsVectorBrownMeasure (e ξ) (e.conjStarAlgEquiv A) μ ↔
      IsVectorBrownMeasure ξ A μ := by
  unfold IsVectorBrownMeasure
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply forall_congr'
  intro z
  have hmap : e.conjStarAlgEquiv (A - z • (1 : E →L[ℂ] E)) =
      e.conjStarAlgEquiv A - z • (1 : F →L[ℂ] F) := by
    simp
  rw [← hmap, vectorFugledeKadisonDeterminant_conj]

end Invariant233

end

end OAI
