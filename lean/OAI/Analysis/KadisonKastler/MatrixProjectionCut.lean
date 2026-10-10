import OAI.Analysis.KadisonKastler.CentralProjectionEnergy
import OAI.Analysis.KadisonKastler.ConjugateVectorSupport
import OAI.Analysis.KadisonKastler.MatrixCentralRefinement

namespace OAI

/-! # A spectral cut supplies the matrix central-vector contraction

A matrix subalgebra containing the cut lies inside its diagonal
central-vector space. The exact discarded-energy identity therefore
gives the contraction estimate used in Haagerup's Lemma 3.6.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem matrixStageCentralProjection_contraction
    (E : FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (p : AlgebraProjection M) (hmem : p.val.val ∈ E.units.concreteAlgebra)
    (η : H) (γ : ℝ)
    (hgap : γ * ‖η‖ ^ 2 ≤ ‖p.val.val η - conjugationOperator J p.val.val η‖ ^ 2) :
    ‖matrixStageCentralProjection E J η‖ ^ 2 ≤ (1 - γ) * ‖η‖ ^ 2 := by
  let K := centralVectorSpace (matrixUnitConcreteAlgebra E.units) J
  have hp : IsStarProjection p.val.val := p.property.map M.toStarSubalgebra.subtype
  have hq : IsStarProjection (conjugationOperator J p.val.val) :=
    (conjugateAlgebraProjection M M.commutant J hJ hright p).property.map
      M.commutant.toStarSubalgebra.subtype
  have hc : Commute p.val.val (conjugationOperator J p.val.val) :=
    VonNeumannAlgebra.mem_commutant_iff.mp (hright p.val) p.val.val p.val.property
  have hK (ξ : H) (hξ : ξ ∈ K) : p.val.val ξ = conjugationOperator J p.val.val ξ := by
    have h := hξ (⟨p.val.val,hmem⟩ : Algebra (matrixUnitConcreteAlgebra E.units))
    change p.val.val ξ = conjugationOperator J (star p.val.val) ξ at h
    rwa [hp.isSelfAdjoint.star_eq] at h
  exact centralProjection_contraction_of_gap K hp hq hc hK η γ hgap

theorem centralProjection_displacement_le_of_central_vector
    (K : Submodule ℂ H) [CompleteSpace K] (ξ ζ : H) (hζ : ζ ∈ K) :
    ‖ξ - K.starProjection ξ‖ ≤ ‖ξ - ζ‖ := by
  have hp := isStarProjection_starProjection (U := K)
  have he : (1 - K.starProjection) (ξ - ζ) = ξ - K.starProjection ξ := by
    simp only [map_sub,sub_apply,one_apply_eq_self,
      Submodule.starProjection_eq_self_iff.mpr hζ,sub_self,sub_zero]
  rw [← he]
  exact projection_apply_norm_le hp.one_sub (ξ - ζ)

end

end KadisonKastler

end OAI
