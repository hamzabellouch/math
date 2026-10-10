import OAI.Analysis.KadisonKastler.MatrixLiftConjugation
import OAI.Analysis.KadisonKastler.FiniteModelEmbedding

namespace OAI

/-! # Diagonal unitary lifts for concretely represented matrix ultrapowers -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {n : ℕ} [NeZero n]
variable {B C : Type*} [CStarAlgebra B] [CStarAlgebra C]
variable {τ : FaithfulTracialState (Algebra M)} {σ : FaithfulTracialState C}
variable {σbase : FaithfulTracialState B} {ω : Ultrafilter ℕ}

local instance matrixQuotientScalarOrder : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance matrixQuotientScalarStarOrder : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing _
local instance matrixQuotientOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance matrixQuotientStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

/-- Present the concrete matrix quotient as a quotient of abstract C⋆-matrices. -/
def TraceQuotientMap.matrixSource
    (R : TraceQuotientMap (matrixVonNeumannTrace (ι := Fin n) M τ) σ ω) :
    TraceQuotientMap (matrixTrace (ι := Fin n) τ) σ ω :=
  R.comapEquiv (matrixAlgebraEquiv M) (matrixVonNeumannTrace_map τ)

/-- The change of representation fixes every constant scalar matrix. -/
theorem TraceQuotientMap.matrixSource_scalar
    (R : TraceQuotientMap (matrixVonNeumannTrace (ι := Fin n) M τ) σ ω)
    (a : CStarMatrix (Fin n) (Fin n) ℂ) :
    R.matrixSource.quotient
        (boundedSequenceConst (coefficientMatrixMap (StarAlgHom.ofId ℂ (Algebra M)) a)) =
      R.constant (concreteScalarMatrixHom (M := M) a) := by
  change R.quotient
      (boundedSequenceMapHom (matrixAlgebraEquiv M).toStarAlgHom
        (boundedSequenceConst (coefficientMatrixMap (StarAlgHom.ofId ℂ (Algebra M)) a))) = _
  apply congrArg R.quotient
  apply BoundedContinuousFunction.ext
  intro k
  rfl

/-- A quotient unitary in the scalar-matrix commutant has a concrete
bounded diagonal-unitary lift with coefficients in the original factor. -/
theorem exists_concrete_scalar_commutant_lift
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (Qbase : TraceQuotientMap τ σbase ω)
    (R : TraceQuotientMap (matrixVonNeumannTrace (ι := Fin n) M τ) σ ω)
    (w : unitary C)
    (hw : ∀ a : CStarMatrix (Fin n) (Fin n) ℂ,
      R.constant (concreteScalarMatrixHom (M := M) a) * (w : C) =
        (w : C) * R.constant (concreteScalarMatrixHom (M := M) a)) :
    ∃ z : unitary (BoundedSequence (Algebra M)),
      R.quotient (concreteDiagonalSequence (n := n) (z : BoundedSequence (Algebra M))) =
        (w : C) := by
  have hh : ∀ a : CStarMatrix (Fin n) (Fin n) ℂ,
      R.matrixSource.quotient
          (boundedSequenceConst (coefficientMatrixMap (StarAlgHom.ofId ℂ (Algebra M)) a)) *
          (w : C) =
        (w : C) * R.matrixSource.quotient
          (boundedSequenceConst (coefficientMatrixMap (StarAlgHom.ofId ℂ (Algebra M)) a)) := by
    intro a
    simpa only [TraceQuotientMap.matrixSource_scalar] using hw a
  obtain ⟨z, hz⟩ := exists_scalar_commutant_unitary_lift hM Qbase R.matrixSource w hh
  exact ⟨z, hz⟩

end

end KadisonKastler

end OAI
