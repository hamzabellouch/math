import OAI.Analysis.KadisonKastler.CentralVectorSpace
import OAI.Analysis.KadisonKastler.DecreasingHilbertProjections
import OAI.Analysis.KadisonKastler.MatrixClosureExpectation

namespace OAI

/-! # Central vectors of an increasing matrix sequence

The decreasing central-vector projections have an actual strong limit.
When their common range is a separating line, the state and commutant
identities supply the exact expected-subfactor model.
-/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def matrixCentralVectorSpace (A : ℕ → FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H) :
    Submodule ℂ H := ⨅ n, centralVectorSpace (matrixUnitConcreteAlgebra (A n).units) J

theorem matrixCentralVectorSpace_isClosed
    (A : ℕ → FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H) :
    IsClosed (matrixCentralVectorSpace A J : Set H) := by
  simp only [matrixCentralVectorSpace, Submodule.coe_iInf]
  exact isClosed_iInter (fun n => centralVectorSpace_isClosed _ J)

instance matrixCentralVectorSpace_complete
    (A : ℕ → FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H) :
    CompleteSpace (matrixCentralVectorSpace A J) :=
  (matrixCentralVectorSpace_isClosed A J).completeSpace_coe

theorem matrixCentralVectorSpace_le
    (A : ℕ → FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H) (n : ℕ) :
    matrixCentralVectorSpace A J ≤ centralVectorSpace (matrixUnitConcreteAlgebra (A n).units) J :=
  iInf_le _ n

theorem matrixCentralVectorSpace_tendsto
    (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) :
    Tendsto (fun n => (centralVectorSpace (matrixUnitConcreteAlgebra (A n).units) J).starProjection ξ)
      atTop (𝓝 ((matrixCentralVectorSpace A J).starProjection ξ)) := by
  have hanti : Antitone (fun n => centralVectorSpace (matrixUnitConcreteAlgebra (A n).units) J) := by
    intro m n hmn
    apply centralVectorSpace_antitone
    exact hA hmn
  obtain ⟨η,hη,ht,ho⟩ := decreasing_projection_limit _ hanti ξ
  have hm : η ∈ matrixCentralVectorSpace A J := (Submodule.mem_iInf _).mpr hη
  have he : (matrixCentralVectorSpace A J).starProjection ξ = η :=
    Submodule.eq_starProjection_of_mem_of_inner_eq_zero hm
      (fun w hw => ho w ((Submodule.mem_iInf _).mp hw))
  rwa [he]

theorem matrixCentralVectorSpace_centralizes
    (A : ℕ → FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : ξ ∈ matrixCentralVectorSpace A J) :
    ∀ n a, a ∈ (A n).units.concreteAlgebra → ∀ x : Algebra M,
      inner ℂ ξ ((a * x.val) ξ) = inner ℂ ξ ((x.val * a) ξ) := by
  intro n a ha x
  let N := matrixUnitConcreteAlgebra (A n).units
  exact vector_functional_centralizes_of_conjugate_right N M
    (matrixUnitConcreteAlgebra_le (A n).units) J hJ ξ
    (fun r => hright (coordinateInclusion (matrixUnitConcreteAlgebra_le (A n).units) r))
    (matrixCentralVectorSpace_le A J n hξ) ⟨a,ha⟩ x

/-- The rank-one central-vector conclusion gives irreducibility. -/
theorem matrixClosure_irreducible_of_centralVectorSpace
    (A : ℕ → FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : ξ ∈ matrixCentralVectorSpace A J)
    (hline : matrixCentralVectorSpace A J ≤ Submodule.span ℂ {ξ})
    (hsep : Function.Injective (algebraVectorMap M ξ)) :
    ∀ T ∈ M,
      (∀ r ∈ FiniteMatrixStage.generatedVonNeumann A, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H) := by
  intro T hT hcomm
  have hTx : T ξ ∈ matrixCentralVectorSpace A J := by
    apply (Submodule.mem_iInf _).mpr
    intro n
    apply centralVectorSpace_invariant J
      (fun a => hright (coordinateInclusion (matrixUnitConcreteAlgebra_le (A n).units) (star a)))
      T hT
    · intro a
      exact hcomm a.val (FiniteMatrixStage.stage_le_generated A n a.property)
    · exact matrixCentralVectorSpace_le A J n hξ
  obtain ⟨z,hz⟩ := Submodule.mem_span_singleton.mp (hline hTx)
  refine ⟨z, ?_⟩
  have ha : (⟨T,hT⟩ : Algebra M) = z • (1 : Algebra M) := by
    apply hsep
    change T ξ = z • ξ
    exact hz.symm
  exact congrArg Subtype.val ha

/-- A separating central line yields the expectation data. -/
theorem expectedMatrixSubfactorModel_of_central_line [Nontrivial H]
    (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hunit : ‖ξ‖ = 1)
    (hcyc : DenseRange (algebraVectorMap M ξ))
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hξ : ξ ∈ matrixCentralVectorSpace A J)
    (hline : matrixCentralVectorSpace A J ≤ Submodule.span ℂ {ξ}) :
    Nonempty (ExpectedMatrixSubfactorModel M) :=
  expectedMatrixSubfactorModel_of_centralizing_stages A hA ξ hunit hcyc hsep
    (matrixCentralVectorSpace_centralizes A J hJ hright ξ hξ)
    (matrixClosure_irreducible_of_centralVectorSpace A J hright ξ hξ hline hsep)

end

end KadisonKastler

end OAI
