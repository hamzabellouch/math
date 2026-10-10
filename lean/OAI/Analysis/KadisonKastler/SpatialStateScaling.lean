import OAI.Analysis.KadisonKastler.StateScalingAlgebra
import OAI.Analysis.KadisonKastler.SpatialStateCentrality

namespace OAI

/-! # State-scaling identities under spatial inclusions and conjugations -/

namespace KadisonKastler

open Generator UnitalTomsWinter

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  {Ω : H} {ξ : K} {r : ℝ} {a : H →L[ℂ] H}

omit [CompleteSpace K] in
theorem productVectorState_tensor_slice (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :
    productVectorState (tensorVector ξ Ω) T = productVectorState Ω (tensorVectorSlice ξ T) := by
  exact ((tensorVector ξ).adjoint_inner_right Ω (T (tensorVector ξ Ω))).symm

theorem StateScales.spatialLeft (ha : StateScales M Ω r a) :
    StateScales (spatialProductAlgebra M N) (tensorVector ξ Ω) r (spatialLeft a) := by
  intro T hT
  rw [productVectorState_tensor_slice,productVectorState_tensor_slice,
    tensorVectorSlice_mul_right,tensorVectorSlice_mul_left]
  exact ha _ (tensorVectorSlice_mem M N ξ T hT)

theorem productVectorState_spatial_conjugate (U : H ≃ₗᵢ[ℂ] K) (a : H →L[ℂ] H) :
    productVectorState (U Ω) (U.conjStarAlgEquiv a)=productVectorState Ω a := by
  change inner ℂ (U Ω) ((U.conjStarAlgEquiv a) (U Ω))=inner ℂ Ω (a Ω)
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,U.symm_apply_apply,U.inner_map_map]

theorem StateScales.spatial_conjugate (ha : StateScales M Ω r a)
    (U : H ≃ₗᵢ[ℂ] K) :
    StateScales (spatialTransportAlgebra U M) (U Ω) r (U.conjStarAlgEquiv a) := by
  intro b hb
  let c := U.conjStarAlgEquiv.symm b
  have hc : c ∈ M := (mem_spatialTransportAlgebra U M b).mp hb
  have he : b=U.conjStarAlgEquiv c := (U.conjStarAlgEquiv.apply_symm_apply b).symm
  rw [he,← map_mul,← map_mul,productVectorState_spatial_conjugate,
    productVectorState_spatial_conjugate]
  exact ha c hc

end

end KadisonKastler

end OAI
