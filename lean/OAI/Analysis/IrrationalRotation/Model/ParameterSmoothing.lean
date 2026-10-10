import OAI.Analysis.IrrationalRotation.Model.CircleParameters
import OAI.Analysis.IrrationalRotation.Model.CircleSmoothing
import OAI.Analysis.IrrationalRotation.Model.ContinuityCoboundary

namespace OAI

noncomputable section

namespace Invariant233.CircleParameterData

open InvariantProjection.Continuity

def smoothBlock (p : CircleParameterData) (θ : ℝ) (j : ℕ) (x : Circle) : ℝ :=
  ∑ i ∈ p.block j, circleSmoothedDrop (p.C j) (p.alpha θ i) (p.alpha θ i / 4)
    ((p.q i : ℤ) • x)

def rawBlock (p : CircleParameterData) (θ : ℝ) (j : ℕ) (x : Circle) : ℝ :=
  ∑ i ∈ p.block j, p.C j * (⌊p.coordinate i x + p.alpha θ i⌋ : ℝ)

def smoothBlockTransfer (p : CircleParameterData) (θ : ℝ) (j : ℕ) (x : Circle) : ℝ :=
  ∑ i ∈ p.block j, circleSmoothingTransfer (p.C j) (p.alpha θ i / 4)
    ((p.q i : ℤ) • x)

def relocatedBlock (p : CircleParameterData) (θ : ℝ) (j : ℕ) : Circle → ℝ :=
  relocated (Equiv.addRight (θ : Circle)) (p.smoothBlock θ j)
    (fun n x => p.partition j n x) (p.height j)

def relocatedBlockTransfer (p : CircleParameterData) (θ : ℝ) (j : ℕ) : Circle → ℝ :=
  relocationTransfer (Equiv.addRight (θ : Circle)) (p.smoothBlock θ j)
    (fun n x => p.partition j n x) (p.height j)

def relocatedCost (p : CircleParameterData) (θ : ℝ) (x : Circle) : ℝ :=
  ∑' n : ℕ, p.relocatedBlock θ (n + 1) x

end Invariant233.CircleParameterData

end

end OAI
