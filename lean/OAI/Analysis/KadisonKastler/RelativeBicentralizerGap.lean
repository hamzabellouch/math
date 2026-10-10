import OAI.Analysis.KadisonKastler.BicentralizerProjectionGap
import OAI.Analysis.KadisonKastler.RelativeUnitaryStateDefect

namespace OAI

/-! # Bicentralizer projection gaps in the matrix relative algebra

The residual vector is approximated only in the central-vector space.
The original positive cone supplies the relative state-to-vector bound.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance relativeBicentralizerRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem exists_relative_unitary_residual_gap
    (E : MatrixUnitSystem ι (Algebra M))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hcyc : DenseRange (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (ζ : H) (hζ : ζ ∈ modularPositiveCone (M := M) J ξ) (hunit : ‖ζ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ζ))
    (hζE : ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J)
    (hscalar : ∀ b : Algebra E.relativeVonNeumann, stateBicentralizerMember ζ b →
      ∃ z : ℂ, b=z • 1)
    (η : H) (hη : η≠0) (hηE : η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J)
    (horth : inner ℂ ζ η=0) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary (Algebra E.relativeVonNeumann),
      ‖centralVectorDefect J ζ u.val.val‖ < ε ∧
      ‖η‖/2 ≤ ‖centralVectorDefect J η u.val.val‖ := by
  have hcζ := cyclic_of_separating_of_conjugation_fixed J hJ hleft
    (modularPositiveCone_fixed J hright ξ hξ hζ) hsep
  have hηclosure : η ∈ closure (Set.range (algebraVectorMap E.relativeVonNeumann ζ)) := by
    change η ∈ closure (Set.range (fun a : Algebra E.relativeVonNeumann => a.val ζ))
    rw [relative_centralVector_orbit_dense E J hJ hright ζ hζE hcζ]
    exact hηE
  apply exists_unitary_residual_gap_of_state_defect_bound J hJ
    (relative_conjugation_mem_commutant E J hright) ζ hunit
    (relative_centralVectorDefect_unitary_sq_le_stateCommutator E J hJ hright hleft
      ξ hξ hcyc hpos hζ hζE)
    (scalar_stateOrbitHulls_of_stateBicentralizer ζ (relative_vector_separating E ζ hsep) hscalar)
    η hη horth hηclosure ε hε

theorem exists_relative_projection_residual_gap
    (E : MatrixUnitSystem ι (Algebra M))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hcyc : DenseRange (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (ζ : H) (hζ : ζ ∈ modularPositiveCone (M := M) J ξ) (hunit : ‖ζ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ζ))
    (hζE : ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J)
    (hscalar : ∀ b : Algebra E.relativeVonNeumann, stateBicentralizerMember ζ b →
      ∃ z : ℂ, b=z • 1)
    (η : H) (hη : η≠0) (hηE : η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J)
    (horth : inner ℂ ζ η=0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ p : AlgebraProjection E.relativeVonNeumann,
      ‖(p.val.val-conjugationOperator J p.val.val) ζ‖^2 ≤ δ ∧
      (1/128:ℝ)*‖η‖^2 ≤ ‖(p.val.val-conjugationOperator J p.val.val) η‖^2 := by
  obtain ⟨u,huref,hures⟩ := exists_relative_unitary_residual_gap E J hJ hright hleft
    ξ hξ hcyc hpos ζ hζ hunit hsep hζE hscalar η hη hηE horth (δ/64) (by positivity)
  exact exists_scaled_projection_gap_of_central_defect J hJ
    (relative_conjugation_mem_commutant E J hright) ζ η (by rw [hunit]) hη
    (modularPositiveCone_fixed J hright ξ hξ hζ) u.val (norm_unitary_le_one u)
    δ hδ huref hures

end

end KadisonKastler

end OAI
