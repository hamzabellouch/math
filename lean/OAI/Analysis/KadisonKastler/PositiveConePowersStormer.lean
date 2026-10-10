import OAI.Analysis.KadisonKastler.PositiveConeSelfDual
import OAI.Analysis.KadisonKastler.PositiveConeStateEstimate

namespace OAI

/-! # Powers–Størmer estimate for the generated modular cone

Orthogonal positive decomposition follows from the constructed self-duality.
The support-reflection estimate then proves Araki's Theorem 4(8) in precisely
the represented cyclic setting used for matrix preparation.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance powersStormerRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem exists_positiveCone_orthogonal_decomposition
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hcyc : DenseRange (algebraVectorMap M ξ))
    (x : H) (hx : J x=x) :
    ∃ α β : H, α ∈ modularPositiveCone (M := M) J ξ ∧
      β ∈ modularPositiveCone (M := M) J ξ ∧ inner ℝ α β=0 ∧ x=α-β := by
  obtain ⟨α,β,hα,hβJ,hβdual,horth,heq⟩ :=
    exists_positiveCone_dual_decomposition J hright ξ hξ x hx
  exact ⟨α,β,hα,modularPositiveCone_mem_of_dual J hJ hright hleft ξ hξ hcyc hβJ hβdual,
    (real_inner_comm _ _).trans horth,heq⟩

theorem positiveCone_norm_sq_le_state_norm
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hcyc : DenseRange (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η ζ : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hζ : ζ ∈ modularPositiveCone (M := M) J ξ) :
    ‖η-ζ‖^2 ≤ ‖vectorFunctional (M := M) η-vectorFunctional ζ‖ := by
  have hfixed : J (η-ζ)=η-ζ := by
    rw [map_sub,modularPositiveCone_fixed J hright ξ hξ hη,
      modularPositiveCone_fixed J hright ξ hξ hζ]
  obtain ⟨α,β,hα,hβ,horth,heq⟩ := exists_positiveCone_orthogonal_decomposition
    J hJ hright hleft ξ hξ hcyc (η-ζ) hfixed
  exact positiveCone_norm_sq_le_state_norm_of_decomposition
    J hJ hright hleft ξ hξ hpos hη hζ hα hβ horth heq

end

end KadisonKastler

end OAI
