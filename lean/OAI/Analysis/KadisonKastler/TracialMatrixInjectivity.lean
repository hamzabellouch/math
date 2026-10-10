import OAI.Analysis.KadisonKastler.MatrixTraceRetraction
import OAI.Analysis.KadisonKastler.ContractiveWeakLimit
import OAI.Analysis.KadisonKastler.IrreducibleMatrixSubfactor

namespace OAI

/-! # Injectivity of a tracial increasing matrix closure

The finite-stage ambient retractions preserve the given trace. Their
restrictions therefore converge in trace norm to the identity on the weak
closure. A pointwise weak limit is the required ambient projection.
-/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N M : VonNeumannAlgebra H}

/-- Increasing matrix-stage expectations converge on their weak closure. -/
theorem matrixExpectations_tendsto (τ : TracialRepresentation N)
    (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (x : Algebra N) (hx : x.val ∈ FiniteMatrixStage.generated A) :
    Tendsto (fun n => τ.norm₂
      (conditionalExpectation τ
        (matrixUnitConcreteAlgebra_le (A n).units) x - x))
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k,a,ha,happrox⟩ := FiniteMatrixStage.exists_stage_norm₂_approximation
    A hA τ le_rfl x hx (ε / 2) (half_pos hε)
  refine ⟨k,fun n hn => ?_⟩
  let hN : matrixUnitConcreteAlgebra (A n).units ≤ N := matrixUnitConcreteAlgebra_le (A n).units
  have hfix := conditionalExpectation_fixed τ hN a (hA hn ha)
  have hsub := map_sub (conditionalExpectationCLM τ hN) x a
  change conditionalExpectation τ hN (x-a) =
    conditionalExpectation τ hN x - conditionalExpectation τ hN a at hsub
  rw [hfix] at hsub
  have he : conditionalExpectation τ hN x - x =
      conditionalExpectation τ hN (x-a) - (x-a) := by rw [hsub]; abel
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (show 0 ≤ τ.norm₂ _ from norm_nonneg _)]
  change τ.norm₂ (conditionalExpectation τ hN x - x) < ε
  calc
    _ = τ.norm₂ (conditionalExpectation τ hN (x-a) - (x-a)) := congrArg τ.norm₂ he
    _ ≤ τ.norm₂ (conditionalExpectation τ hN (x-a)) + τ.norm₂ (x-a) :=
      norm_sub_le _ _
    _ ≤ 2 * τ.norm₂ (x-a) := by
      have h := conditionalExpectation_norm₂_le τ hN (x-a)
      linarith
    _ < ε := by linarith

/-- The finite matrix retraction, with codomain viewed in ambient operators. -/
def matrixTraceAmbientRetraction [Nontrivial H] (τ : TracialRepresentation N)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (E : MatrixUnitSystem ι (Algebra N)) (o : ι) :
    (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  (matrixUnitConcreteAlgebra E).toStarSubalgebra.toSubalgebra.toSubmodule.subtypeL.comp
    (matrixTraceRetraction τ E o)

/-- The weak closure of increasing full matrix algebras is injective in a
faithful tracial representation. -/
theorem isInjective_tracial_matrix_closure_of_nontrivial [Nontrivial H]
    (τ : TracialRepresentation N) (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra)) :
    IsInjective (FiniteMatrixStage.generatedVonNeumann A) := by
  let F : ℕ → (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) := fun n =>
    letI : Nonempty (Fin (A n).size) := ⟨⟨0,(A n).positive⟩⟩
    matrixTraceAmbientRetraction τ (A n).units ⟨0,(A n).positive⟩
  let τG := restrictedTrace τ (FiniteMatrixStage.generatedVonNeumann_le A)
  apply isInjective_of_trace_approximations τG F
  · intro n
    let : Nonempty (Fin (A n).size) := ⟨⟨0,(A n).positive⟩⟩
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro T
    change ‖matrixTraceRetraction τ (A n).units ⟨0,(A n).positive⟩ T‖ ≤ 1 * ‖T‖
    exact (matrixTraceRetraction τ (A n).units ⟨0,(A n).positive⟩).le_of_opNorm_le
      (matrixTraceRetraction_norm τ (A n).units ⟨0,(A n).positive⟩) T
  · intro n T
    let : Nonempty (Fin (A n).size) := ⟨⟨0,(A n).positive⟩⟩
    exact FiniteMatrixStage.stage_le_generated A n
      (matrixTraceRetraction τ (A n).units ⟨0,(A n).positive⟩ T).property
  · intro a
    let x : Algebra N := coordinateInclusion (FiniteMatrixStage.generatedVonNeumann_le A) a
    have ht := (tendsto_vector_iff_norm₂ τ atTop _ x).mpr
      (matrixExpectations_tendsto τ A hA x a.property)
    convert ht using 1
    · ext n
      let : Nonempty (Fin (A n).size) := ⟨⟨0,(A n).positive⟩⟩
      exact congrArg (fun b : Algebra N => b.val τ.vector)
        (matrixTraceRetraction_eq_expectation τ (A n).units ⟨0,(A n).positive⟩ x).symm
    · rfl

/-- A faithful unit trace vector itself supplies nontriviality of the Hilbert space. -/
theorem isInjective_tracial_matrix_closure
    (τ : TracialRepresentation N) (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra)) :
    IsInjective (FiniteMatrixStage.generatedVonNeumann A) := by
  have hξ : τ.vector ≠ 0 := by
    intro h
    have hn := τ.norm_vector
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  let : Nontrivial H := ⟨⟨τ.vector, 0, hξ⟩⟩
  exact isInjective_tracial_matrix_closure_of_nontrivial τ A hA

/-- A separably represented II₁ factor has an irreducible injective
tracial subfactor. -/
theorem exists_irreducible_injective_subfactor_tracial
    [TopologicalSpace.SeparableSpace H]
    (τ : TracialRepresentation M) (hM : IsII1Factor M.toStarSubalgebra) :
    ∃ (R : VonNeumannAlgebra H) (hRM : R ≤ M),
      IsII1Factor R.toStarSubalgebra ∧ IsInjective R ∧
      (∀ b : Algebra M,
        (∀ r : Algebra R, coordinateInclusion hRM r * b = b * coordinateInclusion hRM r) →
        ∃ c : ℂ, b = c • (1 : Algebra M)) := by
  obtain ⟨R,hRM,hR,hirr,A,hRA,hmono,_⟩ := exists_irreducible_matrix_subfactor τ hM
  refine ⟨R,hRM,hR,?_,hirr⟩
  rw [hRA]
  exact isInjective_tracial_matrix_closure τ A hmono

end

end KadisonKastler

end OAI
