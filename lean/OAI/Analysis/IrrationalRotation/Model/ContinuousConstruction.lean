import OAI.Analysis.IrrationalRotation.Model.BackgroundData
import OAI.Analysis.IrrationalRotation.Model.ParameterSmoothing

namespace OAI

noncomputable section

namespace Invariant233.CircleParameterData

def rawCost (p : CircleParameterData) (θ : ℝ) (x : Circle) : ℝ :=
  ∑' n : ℕ, p.rawBlock θ (n + 1) x

def continuousCost (p : CircleParameterData) (θ : ℝ) (d : BackgroundBumpData θ)
    (x : Circle) : ℝ :=
  backgroundCost d x + ∑' n : ℕ, p.relocatedBlock θ (n + 1) x

def continuousTransfer (p : CircleParameterData) (θ : ℝ) (d : BackgroundBumpData θ)
    (x : Circle) : ℝ :=
  backgroundTransferSum d x - ∑' n : ℕ,
    (p.smoothBlockTransfer θ (n + 1) x + p.relocatedBlockTransfer θ (n + 1) x)

def continuousWeight (p : CircleParameterData) (θ : ℝ) (d : BackgroundBumpData θ) :
    Circle → ℝ :=
  Function.update (fun x => Real.exp (-p.continuousCost θ d x)) 0 0

end Invariant233.CircleParameterData

end

end OAI
