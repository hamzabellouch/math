import OAI.Analysis.KadisonKastler.MatrixTraceRetraction
import OAI.Analysis.KadisonKastler.TomiyamaPositive

namespace OAI

/-! # State-preserving finite matrix retractions

Only the finite matrix algebra lies in the vector-state centralizer. The
ambient algebra need not carry a trace. Compression to a minimal matrix
column and the column resolution preserve the original state.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] {M : VonNeumannAlgebra H}
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (Ω : H) (hsep : ∀ a : Algebra M, a.val Ω = 0 → a = 0)
  (E : MatrixUnitSystem ι (Algebra M)) (o : ι)

include hsep in
omit [Nonempty ι] in
theorem matrixStateVector_ne_zero : (E.entry o o).val Ω ≠ 0 := by
  intro h
  exact E.diagonal_ne_zero o (hsep _ h)

omit [Nontrivial H] [Nonempty ι] in
theorem matrixStateVector_fixed :
    (matrixUnitDiagonalProjection (concreteMatrixUnits E) o).val.val
      ((E.entry o o).val Ω) = (E.entry o o).val Ω := by
  change (E.entry o o).val ((E.entry o o).val Ω) = _
  have h := congrArg (fun a : Algebra M => a.val Ω) (E.mul_entry o o o o)
  simpa only [ite_true, MulMemClass.coe_mul, mul_apply_eq_comp] using h

/-- A minimal matrix column gives a concrete contractive retraction. -/
def matrixStateRetraction : (H →L[ℂ] H) →L[ℂ]
    Algebra (matrixUnitConcreteAlgebra E) :=
  minimalCyclicRetraction (matrixUnitConcreteAlgebra E)
    (scalarCenter_of_matrixUnits_surjective (concreteMatrixUnits E)
      (concreteMatrixUnits_surjective E))
    (matrixUnitDiagonalProjection (concreteMatrixUnits E) o)
    (matrixUnitDiagonalProjection_minimal (concreteMatrixUnits E)
      (concreteMatrixUnits_surjective E) o)
    ((E.entry o o).val Ω) (matrixStateVector_ne_zero Ω hsep E o)
    (matrixStateVector_fixed Ω E o)

theorem matrixStateRetraction_norm : ‖matrixStateRetraction Ω hsep E o‖ ≤ 1 :=
  minimalCyclicRetraction_norm _ _ _ _ _ _ _

@[simp] theorem matrixStateRetraction_fixed (a : Algebra (matrixUnitConcreteAlgebra E)) :
    matrixStateRetraction Ω hsep E o a.val = a :=
  minimalCyclicRetraction_fixed _ _ _ _ _ _ _ a

omit [Nontrivial H] [Nonempty ι] in
theorem matrixStateColumn_mem (i : ι) :
    (E.entry i o).val Ω ∈
      typeICyclicSpace (matrixUnitConcreteAlgebra E) ((E.entry o o).val Ω) := by
  have h := vectorOrbitClosure_invariant (matrixUnitConcreteAlgebra E).toStarSubalgebra
    ((E.entry o o).val Ω) ((concreteMatrixUnits E).entry i o)
    (mem_vectorOrbitClosure _ _)
  have he : (E.entry i o).val ((E.entry o o).val Ω) = (E.entry i o).val Ω := by
    have hm := congrArg (fun a : Algebra M => a.val Ω) (E.mul_entry i o o o)
    simpa only [ite_true, MulMemClass.coe_mul, mul_apply_eq_comp] using hm
  change (E.entry i o).val ((E.entry o o).val Ω) ∈ _ at h
  rwa [he] at h

omit [Nontrivial H] [Nonempty ι] in
/-- Centrality of the matrix units is enough for the matrix-column identity. -/
theorem matrixColumn_state
    (hcentral : ∀ i j (x : Algebra M),
      inner ℂ Ω ((E.entry i j * x).val Ω) =
        inner ℂ Ω ((x * E.entry i j).val Ω)) (T : Algebra M) :
    (∑ i, inner ℂ ((E.entry i o).val Ω) (T.val ((E.entry i o).val Ω))) =
      inner ℂ Ω (T.val Ω) := by
  have hterm (i : ι) :
      inner ℂ ((E.entry i o).val Ω) (T.val ((E.entry i o).val Ω)) =
        inner ℂ Ω ((T * E.entry i i).val Ω) := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ Ω ((star (E.entry i o) * (T * E.entry i o)).val Ω) = _
    rw [E.star_entry, hcentral, mul_assoc, E.mul_entry, ite_eq_left rfl]
  simp_rw [hterm]
  have hsum : (∑ i, T * E.entry i i) = T := by
    rw [← Finset.mul_sum, E.total, mul_one]
  have h := congrArg (fun a : Algebra M => inner ℂ Ω (a.val Ω)) hsum
  simpa only [AddSubmonoidClass.coe_finsetSum, sum_apply,
    inner_sum] using h

/-- The retraction preserves the ambient vector state on its centralizer domain. -/
theorem matrixStateRetraction_state
    (hcentral : ∀ i j (x : Algebra M),
      inner ℂ Ω ((E.entry i j * x).val Ω) =
        inner ℂ Ω ((x * E.entry i j).val Ω)) (T : Algebra M) :
    inner ℂ Ω ((matrixStateRetraction Ω hsep E o T.val).val Ω) =
      inner ℂ Ω (T.val Ω) := by
  change inner ℂ Ω
    ((coordinateInclusion E.concreteAlgebra_le (matrixStateRetraction Ω hsep E o T.val)).val Ω) = _
  rw [← matrixColumn_state Ω E o hcentral
    (coordinateInclusion E.concreteAlgebra_le (matrixStateRetraction Ω hsep E o T.val))]
  rw [← matrixColumn_state Ω E o hcentral T]
  apply Finset.sum_congr rfl
  intro i _
  exact minimalCyclicRetraction_coefficient _ _ _ _ _ _ _ T.val
    ⟨(E.entry i o).val Ω, matrixStateColumn_mem Ω E o i⟩
    ⟨(E.entry i o).val Ω, matrixStateColumn_mem Ω E o i⟩

theorem matrixStateRetraction_mul_left
    (a : Algebra (matrixUnitConcreteAlgebra E)) (T : H →L[ℂ] H) :
    matrixStateRetraction Ω hsep E o (a.val * T) = a * matrixStateRetraction Ω hsep E o T :=
  minimalCyclicRetraction_mul_left _ _ _ _ _ _ _ a T

theorem matrixStateRetraction_star (T : H →L[ℂ] H) :
    matrixStateRetraction Ω hsep E o (star T) = star (matrixStateRetraction Ω hsep E o T) := by
  apply unital_contraction_map_star
  · intro T
    simpa only [one_mul] using (matrixStateRetraction Ω hsep E o).le_of_opNorm_le
      (matrixStateRetraction_norm Ω hsep E o) T
  · exact matrixStateRetraction_fixed Ω hsep E o 1

theorem matrixStateRetraction_mul_right
    (a : Algebra (matrixUnitConcreteAlgebra E)) (T : H →L[ℂ] H) :
    matrixStateRetraction Ω hsep E o (T * a.val) = matrixStateRetraction Ω hsep E o T * a := by
  have h := congrArg star (matrixStateRetraction_mul_left Ω hsep E o (star a) (star T))
  simpa only [star_mul, StarMemClass.coe_star, ← matrixStateRetraction_star,
    star_star] using h

end

end KadisonKastler

end OAI
