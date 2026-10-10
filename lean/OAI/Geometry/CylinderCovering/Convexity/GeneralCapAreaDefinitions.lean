import Mathlib

namespace OAI

noncomputable section

namespace CylinderCovering.GeneralCapArea

def profile (q : ℝ) : ℝ := (q ^ 2 + q ^ 4) / 16

def idealSpeed (q : ℝ) : ℝ := ((1 + q ^ 2) / 4) ^ 2 + 2 * (q / 2) ^ 2

def idealDensity (ε η q : ℝ) : ℝ :=
  1 / 4 + ε ^ 2 * (profile q + η - idealSpeed q / 8)

def capDensity (ε α β : ℝ) (R : ℝ → ℝ) (q : ℝ) : ℝ :=
  (R q) ^ 2 / Real.sqrt (1 + ε ^ 2 * (α ^ 2 + 2 * β ^ 2))

end CylinderCovering.GeneralCapArea

end

end OAI
