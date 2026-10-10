import OAI.Analysis.KadisonKastler.ModularStripSpectralBoundary
import OAI.Analysis.KadisonKastler.ModularKMSVectors

namespace OAI

/-! # The KMS condition for the constructed modular group

The graph coordinates give both boundary values of a bounded holomorphic
strip. No normalization or commutant theorem is assumed here.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem modularStrongGroup_kms :
    VectorStateKMS M Ω (modularStrongGroup J Ω hsep hcyc) := by
  intro x hx y hy
  let a : Algebra M := ⟨x, hx⟩
  let b : Algebra M := ⟨y, hy⟩
  let X := tomitaCoreCoordinate J Ω hsep hcyc (star a)
  let Y := tomitaCoreCoordinate J Ω hsep hcyc b
  refine ⟨modularSpectralStrip (M := M) J Ω X Y,
    modularSpectralStrip_continuousOn J Ω hsep hcyc X Y,
    modularSpectralStrip_differentiableOn J Ω hsep hcyc X Y,
    modularSpectralStrip_bounded J Ω hsep hcyc X Y, ?_, ?_⟩
  · intro t
    exact (modularSpectralStrip_bottom J Ω hsep hcyc X Y t).trans
      (modularState_lower_resolvent J Ω hsep hcyc t a b).symm
  · intro t
    exact (modularSpectralStrip_top J Ω hsep hcyc X Y t).trans
      (modularState_upper_resolvent J Ω hsep hcyc t a b).symm

theorem modularStrongGroup_isModular :
    IsModularStateGroup M Ω (modularStrongGroup J Ω hsep hcyc) where
  fixes_vector t := modularStrongGroup_fixes_state J Ω hsep hcyc t.toAdd
  kms := modularStrongGroup_kms J Ω hsep hcyc

end

end KadisonKastler

end OAI
