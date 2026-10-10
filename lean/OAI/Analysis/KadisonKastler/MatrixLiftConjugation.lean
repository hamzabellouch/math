import OAI.Analysis.KadisonKastler.MatrixEmbedding
import OAI.Analysis.KadisonKastler.FiniteMatrixFreeModel
import OAI.Analysis.KadisonKastler.MatrixCommutantLifts
import OAI.Analysis.KadisonKastler.SequenceTransport
import Mathlib.Algebra.Star.UnitaryStarAlgAut

namespace OAI

/-! # Conjugating finite-matrix lifts by a diagonal unitary

Conjugating the inner matrix units changes only the finite matrix algebra
in which a representative lies. Both the concrete embedding and its
bounded sequence version respect this conjugation exactly.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {A B ι κ : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

local instance matrixLiftScalarOrder : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance matrixLiftScalarStarOrder : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing _

local instance matrixLiftSourceOrder : PartialOrder A := CStarAlgebra.spectralOrder _
local instance matrixLiftSourceStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing _
local instance matrixLiftTargetOrder : PartialOrder B := CStarAlgebra.spectralOrder _
local instance matrixLiftTargetStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing _

/-- Map the chosen matrix units under the inner star automorphism. -/
def conjugatedMatrixUnits (E : Generator.MatrixUnitSystem ι A) (z : unitary A) :
    Generator.MatrixUnitSystem ι A :=
  E.map (Unitary.conjStarAlgAut ℂ A z).toStarAlgHom

@[simp]
theorem conjugatedMatrixUnits_entry (E : Generator.MatrixUnitSystem ι A)
    (z : unitary A) (i j : ι) :
    (conjugatedMatrixUnits E z).entry i j = (z : A) * E.entry i j * star (z : A) := rfl

/-- Matrix-unit embeddings commute with every star algebra homomorphism. -/
theorem matrixUnitsEmbedding_map_hom (E : Generator.MatrixUnitSystem ι A)
    (φ : A →⋆ₐ[ℂ] B) (x : CStarMatrix ι ι ℂ) :
    matrixUnitsEmbedding (E.map φ) x = φ (matrixUnitsEmbedding E x) := by
  simp only [matrixUnitsEmbedding_apply, Generator.MatrixUnitSystem.map_entry,
    map_sum, map_smul]

@[simp]
theorem matrixScalarHom_mul_apply (a : A) (x : CStarMatrix κ κ A) (i j : κ) :
    (matrixScalarHom (ι := κ) a * x) i j = a * x i j := by
  simp only [CStarMatrix.mul_apply, matrixScalarHom_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

@[simp]
theorem mul_matrixScalarHom_apply (x : CStarMatrix κ κ A) (a : A) (i j : κ) :
    (x * matrixScalarHom (ι := κ) a) i j = x i j * a := by
  simp only [CStarMatrix.mul_apply, matrixScalarHom_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Diagonal conjugation is entrywise conjugation. -/
theorem coefficientMatrixMap_inner (z : unitary A) (x : CStarMatrix κ κ A) :
    coefficientMatrixMap (Unitary.conjStarAlgAut ℂ A z).toStarAlgHom x =
      matrixScalarHom (z : A) * x * star (matrixScalarHom (z : A)) := by
  rw [← map_star]
  apply CStarMatrix.ext
  intro i j
  simp only [coefficientMatrixMap_apply, StarAlgEquiv.toStarAlgHom_apply,
    Unitary.conjStarAlgAut_apply, mul_matrixScalarHom_apply, matrixScalarHom_mul_apply]

/-- The matrix-coefficient embeddings transform by the same diagonal conjugation. -/
theorem coefficientMatrixMap_conjugatedMatrixUnits
    (E : Generator.MatrixUnitSystem ι A) (z : unitary A)
    (x : CStarMatrix κ κ (CStarMatrix ι ι ℂ)) :
    coefficientMatrixMap (matrixUnitsEmbedding (conjugatedMatrixUnits E z)) x =
      matrixScalarHom (z : A) * coefficientMatrixMap (matrixUnitsEmbedding E) x *
        star (matrixScalarHom (z : A)) := by
  rw [← coefficientMatrixMap_inner]
  apply CStarMatrix.ext
  intro i j
  exact matrixUnitsEmbedding_map_hom E (Unitary.conjStarAlgAut ℂ A z).toStarAlgHom (x i j)

section Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {n j : ℕ} [NeZero n]

local instance matrixLiftConcreteOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance matrixLiftConcreteStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

/-- The concrete diagonal amplification of an inner unitary. -/
def concreteDiagonalUnitary (z : unitary (Algebra M)) :
    unitary (Algebra (matrixVonNeumann (ι := Fin n) M)) :=
  Unitary.map (StarMonoidHom.ofClass
    ((matrixAlgebraHom M).comp (matrixScalarHom (ι := Fin n)))) z

omit [NeZero n] in
@[simp]
theorem concreteDiagonalUnitary_coe (z : unitary (Algebra M)) :
    (concreteDiagonalUnitary (n := n) z : Algebra (matrixVonNeumann (ι := Fin n) M)) =
      matrixAlgebraHom M (matrixScalarHom (z : Algebra M)) := rfl

omit [NeZero n] in
/-- Conjugation by the concrete diagonal unitary is exactly the finite
embedding made from the conjugated inner matrix units. -/
theorem finiteMatrixEmbedding_conjugatedMatrixUnits
    (E : Generator.MatrixUnitSystem (Fin (j + 1)) (Algebra M))
    (z : unitary (Algebra M)) (x : FiniteMatrixModel n j) :
    finiteMatrixEmbedding (conjugatedMatrixUnits E z) x =
      (concreteDiagonalUnitary (n := n) z : Algebra (matrixVonNeumann (ι := Fin n) M)) *
        finiteMatrixEmbedding E x * star (concreteDiagonalUnitary (n := n) z :
          Algebra (matrixVonNeumann (ι := Fin n) M)) := by
  change matrixAlgebraHom M
      (coefficientMatrixMap (matrixUnitsEmbedding (conjugatedMatrixUnits E z)) x) = _
  rw [coefficientMatrixMap_conjugatedMatrixUnits, map_mul, map_mul, map_star]
  rfl

/-- The coordinate unitary of a bounded unitary sequence. -/
def matrixLiftUnitaryAt (z : unitary (BoundedSequence (Algebra M))) (k : ℕ) :
    unitary (Algebra M) :=
  Unitary.map (StarMonoidHom.ofClass (boundedSequenceEval (B := Algebra M) k)) z

@[simp]
theorem matrixLiftUnitaryAt_coe (z : unitary (BoundedSequence (Algebra M))) (k : ℕ) :
    (matrixLiftUnitaryAt z k : Algebra M) = (z : BoundedSequence (Algebra M)) k := rfl

/-- Conjugated matrix units are chosen separately at every coordinate. -/
def conjugatedMatrixUnitsSequence
    (E : ∀ k, Generator.MatrixUnitSystem (Fin (k + 1)) (Algebra M))
    (z : unitary (BoundedSequence (Algebra M)))
    (k : ℕ) : Generator.MatrixUnitSystem (Fin (k + 1)) (Algebra M) :=
  conjugatedMatrixUnits (E k) (matrixLiftUnitaryAt z k)

/-- The diagonal bounded sequence, represented on the concrete Hilbert matrix space. -/
def concreteDiagonalSequence (z : BoundedSequence (Algebra M)) :
    BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M)) :=
  boundedSequenceMapHom (matrixAlgebraHom (ι := Fin n) M) (sequenceScalarHom (ι := Fin n) z)

omit [NeZero n] in
@[simp]
theorem concreteDiagonalSequence_apply (z : BoundedSequence (Algebra M)) (k : ℕ) :
    concreteDiagonalSequence (n := n) z k = matrixAlgebraHom M (matrixScalarHom (z k)) := by
  rw [concreteDiagonalSequence, boundedSequenceMapHom_apply]
  congr 1
  apply CStarMatrix.ext
  intro i j
  exact sequenceScalarHom_apply z k i j

/-- The diagonal sequence remains an actual unitary before passing to a quotient. -/
def concreteDiagonalSequenceUnitary (z : unitary (BoundedSequence (Algebra M))) :
    unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) :=
  Unitary.map (StarMonoidHom.ofClass
    ((boundedSequenceMapHom (matrixAlgebraHom (ι := Fin n) M)).comp
      (sequenceScalarHom (ι := Fin n)))) z

omit [NeZero n] in
@[simp]
theorem concreteDiagonalSequenceUnitary_coe
    (z : unitary (BoundedSequence (Algebra M))) :
    (concreteDiagonalSequenceUnitary (n := n) z :
        BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) =
      concreteDiagonalSequence (n := n) (z : BoundedSequence (Algebra M)) := rfl

/-- The second unitary lift preserves the exact finite-matrix representative form. -/
theorem finiteMatrixSequence_conjugatedMatrixUnits
    (E : ∀ k, Generator.MatrixUnitSystem (Fin (k + 1)) (Algebra M))
    (z : unitary (BoundedSequence (Algebra M)))
    (x : VaryingBoundedSequence (FiniteMatrixModel n)) :
    varyingSequenceMap (fun k => finiteMatrixEmbedding (n := n)
        (conjugatedMatrixUnitsSequence E z k)) x =
      concreteDiagonalSequence (n := n) (z : BoundedSequence (Algebra M)) *
        varyingSequenceMap (fun k => finiteMatrixEmbedding (n := n) (E k)) x *
          star (concreteDiagonalSequence (n := n) (z : BoundedSequence (Algebra M))) := by
  apply BoundedContinuousFunction.ext
  intro k
  change finiteMatrixEmbedding (conjugatedMatrixUnits (E k) (matrixLiftUnitaryAt z k)) (x k) =
    concreteDiagonalSequence (n := n) (z : BoundedSequence (Algebra M)) k *
      finiteMatrixEmbedding (E k) (x k) *
        star (concreteDiagonalSequence (n := n) (z : BoundedSequence (Algebra M)) k)
  rw [finiteMatrixEmbedding_conjugatedMatrixUnits, concreteDiagonalSequence_apply]
  rfl

/-- The same identity descends through any star quotient of the bounded sequences. -/
theorem finiteMatrixSequence_conjugatedMatrixUnits_quotient
    {Q : Type*} [CStarAlgebra Q]
    (π : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M)) →⋆ₐ[ℂ] Q)
    (E : ∀ k, Generator.MatrixUnitSystem (Fin (k + 1)) (Algebra M))
    (z : unitary (BoundedSequence (Algebra M)))
    (x : VaryingBoundedSequence (FiniteMatrixModel n)) :
    π (varyingSequenceMap (fun k => finiteMatrixEmbedding (n := n)
        (conjugatedMatrixUnitsSequence E z k)) x) =
      π (concreteDiagonalSequence (n := n) (z : BoundedSequence (Algebra M))) *
        π (varyingSequenceMap (fun k => finiteMatrixEmbedding (n := n) (E k)) x) *
          star (π (concreteDiagonalSequence (n := n) (z : BoundedSequence (Algebra M)))) := by
  simpa only [map_mul, map_star] using
    congrArg π (finiteMatrixSequence_conjugatedMatrixUnits E z x)

end Concrete

end

end KadisonKastler

end OAI
