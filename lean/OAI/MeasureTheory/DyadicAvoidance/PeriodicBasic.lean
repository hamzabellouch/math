import OAI.MeasureTheory.DyadicAvoidance.Model

namespace OAI

noncomputable section

namespace Problem310

def OnePeriodic (H : Set ℝ) : Prop :=
  ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H

def periodDensity (H : Set ℝ) : ENNReal :=
  MeasureTheory.volume (H ∩ Set.Icc (0 : ℝ) 1)

end Problem310

end

end OAI
