import Mathlib

namespace OAI

open Filter Topology Asymptotics
noncomputable section

namespace CylinderCovering.SingularCutoff

def Admissible (p : ℝ) (ρ q : ℝ → ℝ) : Prop :=
  (∀ᶠ c in 𝓝[>] (0 : ℝ), 0 < ρ c ∧ 0 < q c) ∧
  ρ =o[𝓝[>] (0 : ℝ)] (fun c => c) ∧
  Tendsto (fun c => c * (ρ c) ^ (p - 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
  q =o[𝓝[>] (0 : ℝ)] (fun c => c ^ (2 : ℕ)) ∧
  (fun c => c ^ (3 : ℕ)) =o[𝓝[>] (0 : ℝ)] q

def powerCutoff (A β : ℝ) (c : ℝ) : ℝ := (A * c) ^ β

def powerPadding (A B η : ℝ) (c : ℝ) : ℝ := B * (A * c) ^ η

def edgeOneCoefficient (p : ℝ) : ℝ :=
  (2 * p ^ 2 + 10 * p - 13) / (15360 * p)

def boundaryCoefficient (p : ℝ) : ℝ := (2 - p) / 2560 + p / 1536

def energyCoefficient (p : ℝ) : ℝ :=
  (1 / (16 * p)) *
    ((((2 - p) ^ 2 / 80 + p * (2 - p) / 24 + p ^ 2 / 16) / 16) + 1 / 96)

end CylinderCovering.SingularCutoff

end

end OAI
