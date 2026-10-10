import OAI.Analysis.KadisonKastler.FiniteMatrixFreeModel

namespace OAI

/-! # Embedding the finite free model in the factor ultrapower

Coordinate matrix units preserve the trace and the outer scalar matrix
copy. Their induced quotient embedding therefore carries the first free
Haar model to the desired ultrapower, retaining its finite representatives.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {n : ℕ} [NeZero n] {ω : Ultrafilter ℕ}
variable {C : Type*} [CStarAlgebra C] {σ : FaithfulTracialState C}
variable (τ : FaithfulTracialState (Algebra M))

local instance modelEmbeddingScalarOrder : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance modelEmbeddingScalarStarOrder : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing _
local instance modelEmbeddingOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance modelEmbeddingStarOrder : StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

/-- The concrete constant outer scalar matrix copy. -/
def concreteScalarMatrixHom : CStarMatrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
    Algebra (matrixVonNeumann (ι := Fin n) M) :=
  (matrixAlgebraHom M).comp (coefficientMatrixMap (StarAlgHom.ofId ℂ (Algebra M)))

variable (Q : FiniteMatrixUltraproduct n ω)
variable (R : TraceQuotientMap (matrixVonNeumannTrace (ι := Fin n) M τ) σ ω)
variable (E : ∀ j, Generator.MatrixUnitSystem (Fin (j + 1)) (Algebra M))

def FiniteMatrixUltraproduct.modelEmbedding : Algebra Q.algebra →⋆ₐ[ℂ] C :=
  Q.traceQuotient.inducedMap R (fun j => finiteMatrixEmbedding (n := n) (E j))
    (fun j x => finiteMatrixEmbedding_trace (E j) τ x)

theorem FiniteMatrixUltraproduct.modelEmbedding_trace (x : Algebra Q.algebra) :
    σ.toLinearMap (Q.modelEmbedding τ R E x) =
      (concreteFactorTrace Q.factor).toLinearMap x :=
  Q.traceQuotient.trace_inducedMap R (fun j => finiteMatrixEmbedding (n := n) (E j))
    (fun j x => finiteMatrixEmbedding_trace (E j) τ x) x

/-- The quotient embedding fixes the entire scalar matrix base. -/
theorem FiniteMatrixUltraproduct.modelEmbedding_scalar
    (a : CStarMatrix (Fin n) (Fin n) ℂ) :
    Q.modelEmbedding τ R E (Q.scalarHom a) = R.constant (concreteScalarMatrixHom (M := M) a) := by
  have he : varyingSequenceMap (fun j => finiteMatrixEmbedding (n := n) (E j))
      (finiteMatrixScalarSequence a) = boundedSequenceConst (concreteScalarMatrixHom (M := M) a) := by
    apply BoundedContinuousFunction.ext
    intro j
    exact finiteMatrixEmbedding_scalar (E j) a
  exact (Q.traceQuotient.inducedMap_quotient R
    (fun j => finiteMatrixEmbedding (n := n) (E j))
    (fun j x => finiteMatrixEmbedding_trace (E j) τ x) (finiteMatrixScalarSequence a)).trans
      (congrArg R.quotient he)

private theorem modelEmbedding_base :
    Q.scalarHom.range.map (Q.modelEmbedding τ R E) =
      (R.constant.comp (concreteScalarMatrixHom (M := M) (n := n))).range := by
  rw [starAlgHom_range_map]
  congr 1
  exact StarAlgHom.ext (Q.modelEmbedding_scalar τ R E)

/-- The embedded free model retains its coordinate finite-matrix lifts. -/
theorem FiniteMatrixUltraproduct.exists_embedded_freeHaar_lift
    (hind : FiniteBaseIndependence (concreteFactorTrace Q.factor)) :
    ∃ v : unitary (VaryingBoundedSequence (FiniteMatrixModel n)),
      FreeHaarMoments σ
        (R.constant.comp (concreteScalarMatrixHom (M := M) (n := n))).range
        (Unitary.map (StarMonoidHom.ofClass R.quotient)
          (Unitary.map (StarMonoidHom.ofClass
            (varyingSequenceMap (fun j => finiteMatrixEmbedding (n := n) (E j)))) v)) := by
  have hh := map_freeHaar_lift Q.scalarHom.range Q.quotient
    (varyingSequenceMap (fun j => finiteMatrixEmbedding (n := n) (E j))) R.quotient
    (Q.modelEmbedding τ R E) (Q.modelEmbedding_trace τ R E)
    (fun v => Q.traceQuotient.inducedMap_quotient R _ _ v)
    (Q.exists_freeHaar_lift hind)
  rwa [modelEmbedding_base τ Q R E] at hh

end

end KadisonKastler

end OAI
