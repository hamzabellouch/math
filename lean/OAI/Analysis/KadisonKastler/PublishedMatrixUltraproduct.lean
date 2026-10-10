import OAI.Analysis.KadisonKastler.ScalarMatrixTrace
import OAI.Analysis.KadisonKastler.VaryingQuotient

namespace OAI

/-! # The published varying finite-matrix ultraproduct

Popa, *Independence properties in subalgebras of ultraproduct II1
factors*, J. Funct. Anal. 266 (2014), §1.6, printed pp. 7–8
(arXiv:1308.3982v3), recalls the bounded-product quotient and its
canonical trace. For finite factors of dimension tending to infinity,
the result is a II1 factor. Here the coordinates are precisely
M_n(M_(j+1)(C)), the only varying product used in the application.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

local instance matrixProductScalarOrder : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance matrixProductScalarStarOrder : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing _

/-- The represented quotient of the particular finite-matrix sequence.
Only its operator-algebra structure and the canonical trace formula are
assumed; no independent unitary or controlled representative is a field. -/
structure FiniteMatrixUltraproduct (n : ℕ) [NeZero n] (ω : Ultrafilter ℕ) where
  H : Type
  [normedAddCommGroup : NormedAddCommGroup H]
  [innerProductSpace : InnerProductSpace ℂ H]
  [completeSpace : CompleteSpace H]
  algebra : VonNeumannAlgebra H
  factor : Generator.IsII1Factor algebra.toStarSubalgebra
  quotient : VaryingBoundedSequence (FiniteMatrixModel n) →⋆ₐ[ℂ] Algebra algebra
  surjective : Function.Surjective quotient
  trace_limit : ∀ x : VaryingBoundedSequence (FiniteMatrixModel n),
    Tendsto (fun j => (finiteMatrixModelTrace n j).toLinearMap (x j)) (ω : Filter ℕ)
      (𝓝 ((concreteFactorTrace factor).toLinearMap (quotient x)))

attribute [instance] FiniteMatrixUltraproduct.normedAddCommGroup
  FiniteMatrixUltraproduct.innerProductSpace FiniteMatrixUltraproduct.completeSpace

/-- Popa §1.6 specialized to the increasing finite matrix coordinates. -/
def PublishedFiniteMatrixUltraproduct : Prop :=
  ∀ (n : ℕ) [NeZero n] (ω : Ultrafilter ℕ), (ω : Filter ℕ) ≤ atTop →
    Nonempty (FiniteMatrixUltraproduct n ω)

/-- The trace quotient interface used by the constructed coordinate
embedding into the original factor ultrapower. -/
def FiniteMatrixUltraproduct.traceQuotient {n : ℕ} [NeZero n] {ω : Ultrafilter ℕ}
    (Q : FiniteMatrixUltraproduct n ω) :
    VaryingTraceQuotient (finiteMatrixModelTrace n) (concreteFactorTrace Q.factor) ω where
  quotient := Q.quotient
  surjective := Q.surjective
  trace_limit := Q.trace_limit

end

end KadisonKastler

end OAI
