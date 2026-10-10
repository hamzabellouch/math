import OAI.Analysis.KadisonKastler.BicentralizerScalarHulls
import OAI.Analysis.KadisonKastler.UnitaryResidualGap
import OAI.Analysis.KadisonKastler.ScaledCentralProjectionCut

namespace OAI

/-! # Projection residual gaps from a trivial bicentralizer

The weak hull, unitary gap and spectral projection cut are all constructed.
The only hypothesis in this step is the scalar bicentralizer itself.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance bicentralizerProjectionRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem exists_projection_residual_gap_of_bicentralizer
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hunit : ‖ξ‖=1)
    (hcyc : DenseRange (algebraVectorMap M ξ))
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (hscalar : ∀ b : Algebra M, vectorBicentralizerMember J ξ b →
      ∃ z : ℂ, b=z • 1)
    (η : H) (hη : η≠0) (horth : inner ℂ ξ η=0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ p : AlgebraProjection M,
      ‖(p.val.val-conjugationOperator J p.val.val) ξ‖^2 ≤ δ ∧
      (1/128:ℝ)*‖η‖^2 ≤ ‖(p.val.val-conjugationOperator J p.val.val) η‖^2 := by
  have hhull := scalar_stateOrbitHulls_of_bicentralizer
    J hJ hright hleft ξ hξ hcyc hsep hpos hscalar
  obtain ⟨u,huref,hures⟩ := exists_unitary_residual_gap_of_scalar_state_hulls
    J hJ hright hleft ξ hξ hunit hcyc hpos hhull η hη horth (δ/64) (by positivity)
  exact exists_scaled_projection_gap_of_central_defect J hJ hright ξ η
    (by rw [hunit]) hη hξ u.val (norm_unitary_le_one u) δ hδ huref hures

end

end KadisonKastler

end OAI
