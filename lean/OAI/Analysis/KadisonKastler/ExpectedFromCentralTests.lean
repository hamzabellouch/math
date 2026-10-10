import OAI.Analysis.KadisonKastler.ExpectedFromCentralLine
import OAI.Analysis.KadisonKastler.NormalizeCentralLine
import OAI.Analysis.KadisonKastler.CentralLineApproximation

namespace OAI

/-! # From finite central-vector tests to the expected subfactor

Uniform displacement below one keeps the strong-limit vector nonzero.
Vanishing errors on a dense sequence force the central line. Normalization
and the support transfer then give all expected-subfactor data.
-/

namespace KadisonKastler

open Generator Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem expectedMatrixSubfactorModel_of_central_tests
    (hM : TypeIIIFactor M) (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hleft : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hright : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hunit : ‖ξ‖ = 1) (hJξ : J ξ = ξ)
    (η : ℕ → H) (hdense : DenseRange η) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) (δ : ℝ) (hδ : δ < 1)
    (hdisp : ∀ n, ‖ξ - (centralVectorSpace (matrixUnitConcreteAlgebra (A n).units) J).starProjection ξ‖ ≤ δ)
    (htest : ∀ n i, i ≤ n → ∃ c : ℂ,
      ‖(centralVectorSpace (matrixUnitConcreteAlgebra (A n).units) J).starProjection (η i) -
        c • (centralVectorSpace (matrixUnitConcreteAlgebra (A n).units) J).starProjection ξ‖ ≤ ε n) :
    Nonempty (ExpectedMatrixSubfactorModel M) := by
  let K := matrixCentralVectorSpace A J
  let ζ := K.starProjection ξ
  have hζ : ζ ∈ K := K.starProjection_apply_mem ξ
  have hne : ζ ≠ 0 := by
    intro hz
    have hb := matrixCentralVectorSpace_displacement_le A hA J ξ δ hdisp
    change ‖ξ - ζ‖ ≤ δ at hb
    rw [hz,sub_zero,hunit] at hb
    exact (not_le_of_gt hδ) hb
  have hJζ : J ζ = ζ := matrixCentralVectorSpace_projection_fixed A J hJ ξ hJξ
  have hline : K ≤ Submodule.span ℂ {ζ} :=
    matrixCentralVectorSpace_le_line_of_dense_tests A J ξ η hdense ε hε htest
  obtain ⟨Ω,hΩ,hJΩ,hΩK,hK⟩ := exists_unit_symmetric_line K J ζ hne hJζ hζ hline
  exact expectedMatrixSubfactorModel_of_supported_central_line hM A hA J hJ hleft hright
    Ω hΩ hJΩ hΩK hK

end

end KadisonKastler

end OAI
