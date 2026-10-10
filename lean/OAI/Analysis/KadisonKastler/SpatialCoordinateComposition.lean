import OAI.Analysis.KadisonKastler.SpatialConjugacyTransport
import OAI.Analysis.KadisonKastler.RepresentationCommutantInclusion
import OAI.Analysis.KadisonKastler.PublishedCentralDecomposition

namespace OAI

/-! # Composing the coordinate changes used by central decomposition -/

namespace KadisonKastler

open KadisonSimilarity

noncomputable section

variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

theorem spatialTransportAlgebra_trans (e : H ≃ₗᵢ[ℂ] K) (f : K ≃ₗᵢ[ℂ] L)
    (M : VonNeumannAlgebra H) :
    spatialTransportAlgebra f (spatialTransportAlgebra e M) = spatialTransportAlgebra (e.trans f) M := by
  apply VonNeumannAlgebra.ext
  intro T
  constructor
  · rintro ⟨R, ⟨S, hS, rfl⟩, rfl⟩
    refine ⟨S, hS, ?_⟩
    apply ContinuousLinearMap.ext
    intro v
    rfl
  · rintro ⟨S, hS, rfl⟩
    refine ⟨e.conjStarAlgEquiv S, ⟨S, hS, rfl⟩, ?_⟩
    apply ContinuousLinearMap.ext
    intro v
    rfl

theorem spatialTransport_representation {A : Type*} [CStarAlgebra A]
    (e : H ≃ₗᵢ[ℂ] K) (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    spatialTransportAlgebra e (representationVonNeumannAlgebra σ) =
      representationVonNeumannAlgebra (e.conjStarAlgEquiv.toStarAlgHom.comp σ) := by
  apply VonNeumannAlgebra.ext
  intro T
  rw [mem_spatialTransportAlgebra]
  have h := representation_bicommutant_map_mem_iff e.conjStarAlgEquiv σ
    (e.conjStarAlgEquiv.toStarAlgHom.comp σ) (fun _ => rfl) (e.conjStarAlgEquiv.symm T)
  simpa only [StarAlgEquiv.apply_symm_apply] using h.symm

theorem spatialTransport_generated_range {A : Type*} [CStarAlgebra A]
    (e : H ≃ₗᵢ[ℂ] K) (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    spatialTransportAlgebra e (generatedVonNeumannAlgebra σ.range) =
      generatedVonNeumannAlgebra (e.conjStarAlgEquiv.toStarAlgHom.comp σ).range := by
  rw [← representationVonNeumannAlgebra_eq_generated,
    spatialTransport_representation, representationVonNeumannAlgebra_eq_generated]

theorem ScalarCenter.spatialTransport (e : H ≃ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)
    (hM : ScalarCenter M) : ScalarCenter (spatialTransportAlgebra e M) := by
  rintro _ ⟨T, hT, rfl⟩ hc
  have hcentral : ∀ S ∈ M, S * T = T * S := by
    intro S hS
    apply e.conjStarAlgEquiv.injective
    simp only [map_mul]
    exact hc (e.conjStarAlgEquiv S) ⟨S, hS, rfl⟩
  obtain ⟨z, hz⟩ := hM T hT hcentral
  refine ⟨z, ?_⟩
  change e.conjStarAlgEquiv T = z • (1 : K →L[ℂ] K)
  rw [hz]
  simpa only [Algebra.algebraMap_eq_smul_one, StarAlgEquiv.coe_toAlgEquiv] using
    e.conjStarAlgEquiv.toAlgEquiv.commutes z

end

end KadisonKastler

end OAI
