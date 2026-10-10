import OAI.Analysis.IrrationalRotation.Model.CircleDigitMarginals
import OAI.Analysis.IrrationalRotation.Model.ParameterCircleOperator
import OAI.Analysis.IrrationalRotation.Model.CircleRationalGraphs

namespace OAI

noncomputable section
open MeasureTheory
namespace Invariant233.CircleCoupling

def finiteHybridChoice (N i : ℕ) : Bool := decide (i < N + 1)

def finiteHybridPoint (p : CircleParameterData)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (N : ℕ) : Sample → Circle :=
  hybridPoint p hr (finiteHybridChoice N)

def OrderedCouplingIdentities (p : CircleParameterData) (θ : ℝ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber) : Prop :=
  ∀ j : ℕ, ∀ᵐ ω ∂law p j,
    (1 - F (point p hr true ω)) *
      ratioDiagonal (p.floorCocycle θ) (point p hr false ω, point p hr true ω) *
      F (point p hr false ω) = 0 ∧
    ∀ k : ℤ, 0 < p.floorCocycle θ k (point p hr true ω) /
      p.floorCocycle θ k (point p hr false ω) ∧
      p.floorCocycle θ k (point p hr true ω) /
      p.floorCocycle θ k (point p hr false ω) ≤ 1

end Invariant233.CircleCoupling

end

end OAI
