import OAI.Analysis.KadisonKastler.MinimalCyclicExpectation
import OAI.Analysis.FactorGeneration.Expectations

namespace OAI

/-! # Trace-preserving ambient retractions onto finite matrix algebras

The minimal cyclic space is based at a diagonal matrix unit applied to the
original trace vector. The matrix columns then recover the original trace.
-/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] {M : VonNeumannAlgebra H}
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (τ : TracialRepresentation M) (E : MatrixUnitSystem ι (Algebra M)) (o : ι)

omit [Nontrivial H] [Nonempty ι] in
/-- A matrix-column resolution of the faithful vector trace. -/
theorem matrixColumn_trace (T : Algebra M) :
    (∑ i, inner ℂ ((E.entry i o).val τ.vector)
      (T.val ((E.entry i o).val τ.vector))) = τ.trace T := by
  have hterm (i : ι) :
      inner ℂ ((E.entry i o).val τ.vector) (T.val ((E.entry i o).val τ.vector)) =
        τ.trace (T * E.entry i i) := by
    change inner ℂ (baseVector τ (E.entry i o))
      (baseVector τ (T * E.entry i o)) = _
    rw [baseVector_inner_trace, τ.trace_mul_comm, mul_assoc, E.star_entry,
      E.mul_entry, ite_eq_left rfl]
  simp_rw [hterm]
  change (∑ i, coordinateTraceLinear τ (T * E.entry i i)) = _
  rw [← map_sum, ← Finset.mul_sum, E.total, mul_one]
  rfl

omit [Nonempty ι] in
/-- The diagonal trace vector is nonzero by faithfulness. -/
theorem matrixTraceVector_ne_zero : (E.entry o o).val τ.vector ≠ 0 := by
  intro h
  exact E.diagonal_ne_zero o (τ.separating _ h)

omit [Nontrivial H] [Nonempty ι] in
/-- The chosen diagonal fixes its own trace vector. -/
theorem matrixTraceVector_fixed :
    (matrixUnitDiagonalProjection (concreteMatrixUnits E) o).val.val
      ((E.entry o o).val τ.vector) = (E.entry o o).val τ.vector := by
  change (E.entry o o).val ((E.entry o o).val τ.vector) = _
  have h := congrArg (fun a : Algebra M => a.val τ.vector) (E.mul_entry o o o o)
  simpa only [ite_true, MulMemClass.coe_mul, mul_apply_eq_comp] using h

/-- Ambient compression based at the specified diagonal trace vector. -/
def matrixTraceRetraction : (H →L[ℂ] H) →L[ℂ]
    Algebra (matrixUnitConcreteAlgebra E) :=
  minimalCyclicRetraction (matrixUnitConcreteAlgebra E)
    (scalarCenter_of_matrixUnits_surjective (concreteMatrixUnits E)
      (concreteMatrixUnits_surjective E))
    (matrixUnitDiagonalProjection (concreteMatrixUnits E) o)
    (matrixUnitDiagonalProjection_minimal (concreteMatrixUnits E)
      (concreteMatrixUnits_surjective E) o)
    ((E.entry o o).val τ.vector) (matrixTraceVector_ne_zero τ E o)
    (matrixTraceVector_fixed τ E o)

theorem matrixTraceRetraction_norm : ‖matrixTraceRetraction τ E o‖ ≤ 1 :=
  minimalCyclicRetraction_norm _ _ _ _ _ _ _

@[simp] theorem matrixTraceRetraction_fixed (a : Algebra (matrixUnitConcreteAlgebra E)) :
    matrixTraceRetraction τ E o a.val = a :=
  minimalCyclicRetraction_fixed _ _ _ _ _ _ _ a

omit [Nontrivial H] [Nonempty ι] in
/-- Every matrix column belongs to this minimal cyclic space. -/
theorem matrixColumn_mem (i : ι) :
    (E.entry i o).val τ.vector ∈
      typeICyclicSpace (matrixUnitConcreteAlgebra E) ((E.entry o o).val τ.vector) := by
  have h := vectorOrbitClosure_invariant (matrixUnitConcreteAlgebra E).toStarSubalgebra
    ((E.entry o o).val τ.vector) ((concreteMatrixUnits E).entry i o)
    (mem_vectorOrbitClosure _ _)
  have he : (E.entry i o).val ((E.entry o o).val τ.vector) =
      (E.entry i o).val τ.vector := by
    have hm := congrArg (fun a : Algebra M => a.val τ.vector) (E.mul_entry i o o o)
    simpa only [ite_true, MulMemClass.coe_mul, mul_apply_eq_comp] using hm
  change (E.entry i o).val ((E.entry o o).val τ.vector) ∈ _ at h
  rwa [he] at h

/-- Compression preserves the original trace on the ambient finite algebra. -/
theorem matrixTraceRetraction_trace (T : Algebra M) :
    τ.trace (coordinateInclusion E.concreteAlgebra_le (matrixTraceRetraction τ E o T.val)) =
      τ.trace T := by
  rw [← matrixColumn_trace τ E o]
  rw [← matrixColumn_trace τ E o T]
  apply Finset.sum_congr rfl
  intro i _
  exact minimalCyclicRetraction_coefficient _ _ _ _ _ _ _ T.val
    ⟨(E.entry i o).val τ.vector, matrixColumn_mem τ E o i⟩
    ⟨(E.entry i o).val τ.vector, matrixColumn_mem τ E o i⟩

/-- The finite-stage retraction is a left module map over the matrix algebra. -/
theorem matrixTraceRetraction_mul_left
    (a : Algebra (matrixUnitConcreteAlgebra E)) (T : H →L[ℂ] H) :
    matrixTraceRetraction τ E o (a.val * T) = a * matrixTraceRetraction τ E o T :=
  minimalCyclicRetraction_mul_left _ _ _ _ _ _ _ a T

/-- On the finite ambient algebra this is the trace conditional expectation. -/
theorem matrixTraceRetraction_eq_expectation (T : Algebra M) :
    conditionalExpectation τ (matrixUnitConcreteAlgebra_le E) T =
      coordinateInclusion E.concreteAlgebra_le (matrixTraceRetraction τ E o T.val) := by
  apply conditionalExpectation_eq_of_orthogonal
  · exact (matrixTraceRetraction τ E o T.val).property
  · intro b
    let bN : Algebra (matrixUnitConcreteAlgebra E) := ⟨b.val.val, b.property⟩
    have hb : coordinateInclusion E.concreteAlgebra_le bN = b.val := rfl
    have h := matrixTraceRetraction_trace τ E o (b.val * T)
    change τ.trace (coordinateInclusion E.concreteAlgebra_le
      (matrixTraceRetraction τ E o (bN.val * T.val))) = τ.trace (b.val * T) at h
    rw [matrixTraceRetraction_mul_left, map_mul, hb] at h
    change τ.trace (b.val * (T - coordinateInclusion E.concreteAlgebra_le
      (matrixTraceRetraction τ E o T.val))) = 0
    rw [mul_sub, trace_sub, h, sub_self]

end

end KadisonKastler

end OAI
