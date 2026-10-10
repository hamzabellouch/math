import OAI.Analysis.KadisonKastler.MatrixStateRetraction
import OAI.Analysis.KadisonKastler.MatrixClosureVectorTrace
import OAI.Analysis.KadisonKastler.StatePreservingWeakLimit
import OAI.Analysis.KadisonKastler.PublishedExpectedMatrixSubfactor

namespace OAI

/-! # State-preserving expectations onto increasing matrix closures

The finite compressions retain the state on the larger algebra. Taking
their weak limit gives the required expectation on the original space.
-/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-- Centralizing matrix stages give a state-preserving retraction on their closure. -/
theorem exists_matrixClosure_state_retraction [Nontrivial H]
    (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (τ : TracialRepresentation (FiniteMatrixStage.generatedVonNeumann A))
    (hcentral : ∀ n a, a ∈ (A n).units.concreteAlgebra → ∀ x : Algebra M,
      inner ℂ τ.vector ((a * x.val) τ.vector) =
        inner ℂ τ.vector ((x.val * a) τ.vector)) :
    ∃ P : Algebra M →L[ℂ] Algebra (FiniteMatrixStage.generatedVonNeumann A),
      ‖P‖ ≤ 1 ∧
      (∀ a, P (coordinateInclusion (FiniteMatrixStage.generatedVonNeumann_le A) a) = a) ∧
      (∀ a : Algebra M,
        inner ℂ τ.vector ((P a).val τ.vector) = inner ℂ τ.vector (a.val τ.vector)) := by
  let B := matrixStagesInClosure A
  have hB : Monotone (fun n => (B n).units.concreteAlgebra) := by
    simpa only [B, matrixStagesInClosure_algebra] using hA
  let F : ℕ → (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) := fun n =>
    letI : Nonempty (Fin (B n).size) := ⟨⟨0,(B n).positive⟩⟩
    matrixTraceAmbientRetraction τ (B n).units ⟨0,(B n).positive⟩
  apply exists_state_preserving_weak_retraction
    (FiniteMatrixStage.generatedVonNeumann_le A) τ F
  · intro n
    let : Nonempty (Fin (B n).size) := ⟨⟨0,(B n).positive⟩⟩
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro T
    exact (matrixTraceRetraction τ (B n).units ⟨0,(B n).positive⟩).le_of_opNorm_le
      (matrixTraceRetraction_norm τ (B n).units ⟨0,(B n).positive⟩) T
  · intro n T
    let : Nonempty (Fin (B n).size) := ⟨⟨0,(B n).positive⟩⟩
    exact matrixUnitConcreteAlgebra_le (B n).units
      (matrixTraceRetraction τ (B n).units ⟨0,(B n).positive⟩ T).property
  · intro a
    have ha : a.val ∈ FiniteMatrixStage.generated B := by
      change a.val ∈ FiniteMatrixStage.generatedVonNeumann B
      rw [show FiniteMatrixStage.generatedVonNeumann B =
        FiniteMatrixStage.generatedVonNeumann A from matrixStagesInClosure_generated A]
      exact a.property
    have ht := (tendsto_vector_iff_norm₂ τ atTop _ a).mpr
      (matrixExpectations_tendsto τ B hB a ha)
    convert ht using 1
    ext n
    let : Nonempty (Fin (B n).size) := ⟨⟨0,(B n).positive⟩⟩
    exact congrArg (fun b => b.val τ.vector)
      (matrixTraceRetraction_eq_expectation τ (B n).units ⟨0,(B n).positive⟩ a).symm
  · intro n T
    let : Nonempty (Fin (A n).size) := ⟨⟨0,(A n).positive⟩⟩
    let : Nonempty (Fin (B n).size) := ⟨⟨0,(B n).positive⟩⟩
    let o : Fin (A n).size := ⟨0,(A n).positive⟩
    have hc (i j : Fin (A n).size) (x : Algebra M) :
        inner ℂ τ.vector (((A n).units.entry i j * x).val τ.vector) =
          inner ℂ τ.vector ((x * (A n).units.entry i j).val τ.vector) :=
      hcentral n _ (((A n).units.mem_concreteAlgebra _).mpr
        ((A n).units.entry_mem i j)) x
    let Q := matrixTraceRetraction τ (B n).units o
    have hQM : (Q T.val).val ∈ M :=
      FiniteMatrixStage.generatedVonNeumann_le A
        (matrixUnitConcreteAlgebra_le (B n).units (Q T.val).property)
    change inner ℂ τ.vector ((Q T.val).val τ.vector) = _
    rw [← matrixColumn_state τ.vector (A n).units o hc ⟨(Q T.val).val,hQM⟩]
    rw [← matrixColumn_state τ.vector (A n).units o hc T]
    apply Finset.sum_congr rfl
    intro i _
    exact minimalCyclicRetraction_coefficient _ _ _ _ _ _ _ T.val
      ⟨((B n).units.entry i o).val τ.vector, matrixColumn_mem τ (B n).units o i⟩
      ⟨((B n).units.entry i o).val τ.vector, matrixColumn_mem τ (B n).units o i⟩

/-- Centralizing matrix stages yield an expectation and a faithful trace. -/
theorem expectedMatrixSubfactorModel_of_centralizing_stages [Nontrivial H]
    (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (Ω : H) (hΩ : ‖Ω‖ = 1)
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcentral : ∀ n a, a ∈ (A n).units.concreteAlgebra → ∀ x : Algebra M,
      inner ℂ Ω ((a * x.val) Ω) = inner ℂ Ω ((x.val * a) Ω))
    (hirr : ∀ T ∈ M,
      (∀ r ∈ FiniteMatrixStage.generatedVonNeumann A, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H)) :
    Nonempty (ExpectedMatrixSubfactorModel M) := by
  have hsep0 (a : Algebra M) (ha : a.val Ω = 0) : a = 0 := by
    apply hsep
    simpa only [algebraVectorMap, LinearMap.coe_mk, AddHom.coe_mk, ZeroMemClass.coe_zero,
      zero_apply] using ha
  let σ := matrixClosureVectorTrace A hA Ω hΩ hsep0 hcentral
  let τ := tracialRepresentationOfVectorState σ Ω (fun _ => rfl)
  obtain ⟨P,hP,hfix,hstate⟩ := exists_matrixClosure_state_retraction A hA τ hcentral
  obtain ⟨hleft,hright⟩ := retraction_bimodule
    (FiniteMatrixStage.generatedVonNeumann_le A) P hP hfix
  refine ⟨{
    stage := A
    increasing := hA
    trace := σ
    expectation := P
    unital := ?_
    left_module := hleft
    right_module := hright
    vector := Ω
    vector_state := ?_
    cyclic := hcyc
    separating := hsep
    irreducible := hirr }⟩
  · simpa only [map_one] using hfix 1
  · intro x
    exact hstate x

end

end KadisonKastler

end OAI
