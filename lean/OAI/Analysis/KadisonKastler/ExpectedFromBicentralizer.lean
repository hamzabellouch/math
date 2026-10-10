import OAI.Analysis.KadisonKastler.ExpectedFromRelativeBicentralizers
import OAI.Analysis.KadisonKastler.RelativeMatrixSpatial
import OAI.Analysis.KadisonKastler.SpatialBicentralizer

namespace OAI

/-! # The expected subfactor from the ambient state properties

The relative algebras require no additional homogeneity or bicentralizer
assumptions: both properties transfer through the constructed spatial
matrix-corner isomorphism.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance expectedBicentralizerRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem expectedMatrixSubfactorModel_of_bicentralizer
    (hM : TypeIIIFactor M) (ξ : H) (hunit : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hcyc : DenseRange (algebraVectorMap M ξ)) (d : ModularConjugationData M ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic d.conjugation a ξ))
    (hhom : FaithfulVectorStateHomogeneity M)
    (hscalar : FaithfulVectorBicentralizersScalar M) :
    Nonempty (ExpectedMatrixSubfactorModel M) := by
  have ht (E : FiniteMatrixStage M) :
      ∃ (e : Algebra M ≃⋆ₐ[ℂ] Algebra E.units.relativeVonNeumann) (W : H ≃ₗᵢ[ℂ] H),
        ∀ (a : Algebra M) (x : H), W (a.val x)=(e a).val (W x) := by
    obtain ⟨e,u,he⟩ := hM.exists_relative_matrix_spatial_equiv E d.conjugation d.involutive
      (d.right_mem le_rfl)
    exact ⟨e,Unitary.linearIsometryEquiv u,intertwines_of_unitaryConj e u he⟩
  choose e W hW using ht
  apply expectedMatrixSubfactorModel_of_relative_bicentralizers hM ξ hunit hsep hcyc d hpos
  · intro E
    exact hhom.spatial_transport (e E) (W E) (hW E)
  · intro E ω _ hωunit hωsep _
    let : Nonempty (Fin E.size) := ⟨⟨0,E.positive⟩⟩
    exact hscalar.spatial_transport (e E) (W E) (hW E) ω hωunit
      (relative_vector_separating E.units ω hωsep)

end

end KadisonKastler

end OAI
