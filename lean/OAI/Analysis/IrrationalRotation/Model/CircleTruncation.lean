import OAI.Analysis.IrrationalRotation.Model.CircleTruncationEvent
import OAI.Analysis.IrrationalRotation.Model.ConditionalConvolution
import OAI.Analysis.IrrationalRotation.Model.Rotation

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Invariant233.CircleCoupling

def projectionDiagonal (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber)
    (x : Circle) : ℝ := ((F x (lp.single 2 0 1)) 0).re

def projectionCoefficientA (θ : ℝ) (p : CircleParameterData)
    (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber) (x : Circle) (v : ℤ) : ℂ :=
  (F x (lp.single 2 0 1)) v / (p.floorCocycle θ v x : ℂ)

def projectionCoefficientB (θ : ℝ) (p : CircleParameterData)
    (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber) (y : Circle) (v : ℤ) : ℂ :=
  (p.floorCocycle θ (-v) y : ℂ) * conj (((1 - F y) (lp.single 2 0 1)) (-v))

def truncationSum (θ : ℝ) (p : CircleParameterData) (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber) (ω : Sample) : ℝ :=
  ∑ n ∈ Finset.range (2 * p.K j + 1),
    ‖InvariantProjection.ConditionalConvolution.truncated (p.K j) n
      (projectionCoefficientA θ p F (point p hr false ω))
      (projectionCoefficientB θ p F (point p hr true ω))‖

def TruncationBounds (θ : ℝ) (p : CircleParameterData)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber) : Prop :=
  ∃ J : ℕ, 1 ≤ J ∧ ∀ j : ℕ, J ≤ j →
    Real.exp (-90) / 2 ≤ (law p j).real (truncationEvent p j hr (projectionDiagonal F)) ∧
    (Real.exp (-90) / 2) * p.ε j ≤
      ∫ ω in truncationEvent p j hr (projectionDiagonal F),
        truncationSum θ p j hr F ω ∂law p j

end Invariant233.CircleCoupling

end

end OAI
