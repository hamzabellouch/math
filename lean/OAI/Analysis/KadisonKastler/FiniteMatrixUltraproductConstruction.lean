import OAI.Analysis.KadisonKastler.FiniteMatrixProductProjections
import OAI.Analysis.KadisonKastler.TracialSequenceFactor
import OAI.Analysis.KadisonKastler.PublishedMatrixUltraproduct
import OAI.Analysis.KadisonKastler.ConcreteTraceUniqueness

namespace OAI

/-! # The required growing finite-matrix tracial ultraproduct -/

namespace KadisonKastler

open Filter

noncomputable section

local instance : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing _

def constructedFiniteMatrixUltraproduct (n : ℕ) [NeZero n]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop) : FiniteMatrixUltraproduct n ω := by
  let d := constructedTracialSequenceFactor (finiteMatrixModelTrace n) ω hω
    (fun j x => finiteMatrixModel_variance_control n j x)
    (finiteMatrixTracialQuotient_infinite n ω hω)
  exact {
    H := d.H
    algebra := d.algebra
    factor := d.factor
    quotient := d.quotient
    surjective := d.surjective
    trace_limit := d.trace_limit }

/-- Popa §1.6 for the precise finite-matrix sequence used in the application. -/
theorem publishedFiniteMatrixUltraproduct : PublishedFiniteMatrixUltraproduct := by
  intro n _ ω hω
  exact ⟨constructedFiniteMatrixUltraproduct n ω hω⟩

end

end KadisonKastler

end OAI
