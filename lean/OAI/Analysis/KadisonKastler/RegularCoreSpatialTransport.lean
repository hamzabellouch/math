import OAI.Analysis.KadisonKastler.PointwiseL2Spatial
import OAI.Analysis.KadisonKastler.RegularCoreAlgebra

namespace OAI

/-! # Spatial transport of the concrete regular core

Intertwining the original unitary groups transports both kinds of core
generators. This result concerns the actual generated von Neumann algebras.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (V : H ≃ₗᵢ[ℂ] K)
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (W : Multiplicative ℝ →* unitary (K →L[ℂ] K))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (hW : ∀ x, Continuous (fun t : ℝ => (W (Multiplicative.ofAdd t) : K →L[ℂ] K) x))
  (hV : ∀ t x, V ((U t : H →L[ℂ] H) x) = (W t : K →L[ℂ] K) (V x))

include hV in
theorem pointwiseL2Unitary_embedding_apply (a : H →L[ℂ] H) (f : RegularCoreHilbert H) :
    pointwiseL2Unitary V (regularCoreEmbedding U hU a f) =
      regularCoreEmbedding W hW (V.conjStarAlgEquiv a) (pointwiseL2Unitary V f) := by
  apply Lp.ext
  filter_upwards [pointwiseL2Unitary_apply_ae V (regularCoreEmbedding U hU a f),
    regularCoreEmbedding_apply_ae U hU a f,
    regularCoreEmbedding_apply_ae W hW (V.conjStarAlgEquiv a) (pointwiseL2Unitary V f),
    pointwiseL2Unitary_apply_ae V f] with t hv hu hw hf
  rw [hv, hu, hw, hf]
  have hs (x : H) : V ((star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) x) =
      (star (W (Multiplicative.ofAdd t)) : K →L[ℂ] K) (V x) := by
    rw [← Unitary.coe_star, ← Unitary.coe_star,
      regularGroup_star_eq, regularGroup_star_eq]
    exact hV _ x
  rw [hs, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, ← hV,
    LinearIsometryEquiv.symm_apply_apply]

include hV in
theorem pointwiseL2Unitary_embedding (a : H →L[ℂ] H) :
    (pointwiseL2Unitary V).conjStarAlgEquiv (regularCoreEmbedding U hU a) =
      regularCoreEmbedding W hW (V.conjStarAlgEquiv a) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    pointwiseL2Unitary_embedding_apply V U W hU hW hV,
    LinearIsometryEquiv.apply_symm_apply]

include hV in
theorem regularCore_spatialTransport (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (hMN : spatialTransportAlgebra V M = N) :
    spatialTransportAlgebra (pointwiseL2Unitary V) (regularCoreAlgebra U hU M) =
      regularCoreAlgebra W hW N := by
  have hr : (pointwiseL2Unitary V).conjStarAlgEquiv '' regularCoreGenerators U hU M =
      regularCoreGenerators W hW N := by
    ext a
    constructor
    · rintro ⟨_, (⟨b, hb, rfl⟩ | ⟨s, rfl⟩), rfl⟩
      · left
        refine ⟨V.conjStarAlgEquiv b, ?_, (pointwiseL2Unitary_embedding V U W hU hW hV b).symm⟩
        rw [← hMN]
        exact ⟨b, hb, rfl⟩
      · right
        exact ⟨s, (pointwiseL2Unitary_translation V s).symm⟩
    · rintro (⟨b, hb, rfl⟩ | ⟨s, rfl⟩)
      · rw [← hMN] at hb
        rcases hb with ⟨b, hb, rfl⟩
        exact ⟨regularCoreEmbedding U hU b, Or.inl ⟨b, hb, rfl⟩,
          pointwiseL2Unitary_embedding V U W hU hW hV b⟩
      · exact ⟨_, Or.inr ⟨s, rfl⟩, pointwiseL2Unitary_translation V s⟩
  unfold regularCoreAlgebra
  rw [spatialTransport_generated, StarAlgHom.map_adjoin]
  exact congrArg (fun s => generatedVonNeumannAlgebra (StarAlgebra.adjoin ℂ s)) hr

include hV in
theorem regularCore_equiv_of_spatial (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (hMN : spatialTransportAlgebra V M = N) :
    Nonempty (Algebra (regularCoreAlgebra U hU M) ≃⋆ₐ[ℂ]
      Algebra (regularCoreAlgebra W hW N)) := by
  have e := spatialTransportEquiv (pointwiseL2Unitary V) (regularCoreAlgebra U hU M)
  rw [regularCore_spatialTransport V U W hU hW hV M N hMN] at e
  exact ⟨e⟩

end

end KadisonKastler

end OAI
