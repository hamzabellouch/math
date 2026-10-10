import OAI.Analysis.KadisonKastler.MatrixCommutant
import OAI.Analysis.KadisonKastler.UnitaryLifts

namespace OAI

/-! # Unitary lifts respecting the scalar matrix commutant

The matrix ultrapower equivalence identifies the scalar-matrix commutant
with the diagonal coefficient quotient. The proved coordinatewise finite
polar construction then gives a lift which is diagonal at every coordinate.
-/

namespace KadisonKastler

noncomputable section

variable {A B C ι : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
  [Fintype ι] [DecidableEq ι]

local instance diagonalLiftSourceOrder : PartialOrder A := CStarAlgebra.spectralOrder _
local instance diagonalLiftSourceStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing _
local instance diagonalLiftSequenceOrder : PartialOrder (BoundedSequence A) :=
  CStarAlgebra.spectralOrder _
local instance diagonalLiftSequenceStarOrder : StarOrderedRing (BoundedSequence A) :=
  CStarAlgebra.spectralOrderedRing _
local instance diagonalLiftTargetOrder : PartialOrder B := CStarAlgebra.spectralOrder _
local instance diagonalLiftTargetStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing _
local instance diagonalLiftComplexOrder : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance diagonalLiftComplexStarOrder : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing _

/-- Diagonal amplification of a bounded sequence, as an actual star homomorphism. -/
def sequenceScalarHom : BoundedSequence A →⋆ₐ[ℂ] BoundedSequence (CStarMatrix ι ι A) :=
  (sequenceMatrixEquiv (B := A) (ι := ι)).symm.toStarAlgHom.comp matrixScalarHom

@[simp]
theorem sequenceScalarHom_apply (x : BoundedSequence A) (k : ℕ) (i j : ι) :
    sequenceScalarHom x k i j = if i = j then x k else 0 := by
  have h := congrArg (fun m : CStarMatrix ι ι (BoundedSequence A) => m i j k)
    ((sequenceMatrixEquiv (B := A) (ι := ι)).apply_symm_apply (matrixScalarHom x))
  change (sequenceMatrixEquiv.symm (matrixScalarHom x)) k i j = _
  change (sequenceMatrixEquiv.symm (matrixScalarHom x)) k i j =
    (if i = j then x else 0) k at h
  by_cases hij : i = j
  · simpa only [hij, ite_true] using h
  · simp only [hij, ite_false] at h ⊢
    exact h.trans (map_zero (boundedSequenceEval (B := A) k))

variable [Nonempty ι] {τ : FaithfulTracialState A} {σ : FaithfulTracialState B}
  {ρ : FaithfulTracialState C} {ω : Ultrafilter ℕ}

theorem matrixUltrapowerEquiv_sequenceScalar (Q : TraceQuotientMap τ σ ω)
    (P : TraceQuotientMap (matrixTrace (ι := ι) τ) ρ ω) (x : BoundedSequence A) :
    matrixUltrapowerEquiv Q P (P.quotient (sequenceScalarHom x)) =
      matrixScalarHom (Q.quotient x) := by
  apply CStarMatrix.ext
  intro i j
  rw [matrixUltrapowerEquiv_quotient, matrixScalarHom_apply]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    congr 1
    apply BoundedContinuousFunction.ext
    intro k
    simp only [matrixEntrySequence_apply, sequenceScalarHom_apply, ite_true]
  · simp only [hij, ite_false]
    have hz : matrixEntrySequence (sequenceScalarHom x) i j = 0 := by
      apply BoundedContinuousFunction.ext
      intro k
      simp only [matrixEntrySequence_apply, sequenceScalarHom_apply, hij, ite_false]
      rfl
    rw [hz, map_zero]

/-- The matrix-ultrapower identification fixes the scalar matrix copy. -/
theorem matrixUltrapowerEquiv_scalarMatrix (Q : TraceQuotientMap τ σ ω)
    (P : TraceQuotientMap (matrixTrace (ι := ι) τ) ρ ω) (s : CStarMatrix ι ι ℂ) :
    matrixUltrapowerEquiv Q P
      (P.quotient (boundedSequenceConst (coefficientMatrixMap (StarAlgHom.ofId ℂ A) s))) =
        coefficientMatrixMap (StarAlgHom.ofId ℂ B) s := by
  apply CStarMatrix.ext
  intro i j
  rw [matrixUltrapowerEquiv_constant]
  change Q.quotient (algebraMap ℂ (BoundedSequence A) (s i j)) = algebraMap ℂ B (s i j)
  exact AlgHomClass.commutes Q.quotient (s i j)

section Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {τM : FaithfulTracialState (Algebra M)}

local instance diagonalLiftConcreteOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance diagonalLiftConcreteStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

/-- A unitary commuting with the constant scalar matrices has unitary
representatives commuting with those matrices at every coordinate. -/
theorem exists_scalar_commutant_unitary_lift
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (Q : TraceQuotientMap τM σ ω)
    (P : TraceQuotientMap (matrixTrace (ι := ι) τM) ρ ω)
    (u : unitary C)
    (hu : ∀ s : CStarMatrix ι ι ℂ,
      P.quotient (boundedSequenceConst (coefficientMatrixMap (StarAlgHom.ofId ℂ (Algebra M)) s)) *
          (u : C) =
        (u : C) * P.quotient
          (boundedSequenceConst (coefficientMatrixMap (StarAlgHom.ofId ℂ (Algebra M)) s))) :
    ∃ v : unitary (BoundedSequence (Algebra M)),
      P.quotient (sequenceScalarHom (v : BoundedSequence (Algebra M))) = (u : C) := by
  let e := matrixUltrapowerEquiv Q P
  let eu : unitary (CStarMatrix ι ι B) := Unitary.map (StarMonoidHom.ofClass e.toStarAlgHom) u
  have heu : ∀ s : CStarMatrix ι ι ℂ,
      coefficientMatrixMap (StarAlgHom.ofId ℂ B) s * (eu : CStarMatrix ι ι B) =
        (eu : CStarMatrix ι ι B) * coefficientMatrixMap (StarAlgHom.ofId ℂ B) s := by
    intro s
    change coefficientMatrixMap (StarAlgHom.ofId ℂ B) s * e (u : C) =
      e (u : C) * coefficientMatrixMap (StarAlgHom.ofId ℂ B) s
    have h := congrArg e (hu s)
    change matrixUltrapowerEquiv Q P (_ * _) = matrixUltrapowerEquiv Q P (_ * _) at h
    simpa only [map_mul, matrixUltrapowerEquiv_scalarMatrix] using h
  obtain ⟨v, hv⟩ := exists_unitary_matrixScalarHom_of_commutes eu heu
  obtain ⟨w, hw⟩ := exists_unitary_sequence_lift hM Q.quotient Q.surjective v
  refine ⟨w, e.injective ?_⟩
  change matrixUltrapowerEquiv Q P
      (P.quotient (sequenceScalarHom (w : BoundedSequence (Algebra M)))) = e (u : C)
  rw [matrixUltrapowerEquiv_sequenceScalar, hw]
  exact hv.symm

end Concrete

end

end KadisonKastler

end OAI
