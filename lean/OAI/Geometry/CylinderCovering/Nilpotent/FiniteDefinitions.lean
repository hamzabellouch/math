import OAI.Geometry.CylinderCovering.Nilpotent.BasicDefinitions
import OAI.Geometry.RuledCovering.Model

namespace OAI

noncomputable section
open Set
namespace CylinderCovering.Nilpotent
open RuledApproximation

def angularField (κ : ℝ) (b : Plane) : Plane :=
  vec2 (κ * v (b 0 / b 1)) (κ * w (b 0 / b 1))

def truncatedLabels (k ρ : ℝ) : Set Plane :=
  {b | ∃ p t : ℝ, |p| ≤ 1 ∧ ρ ≤ t ∧ t ≤ height k p ∧ b = vec2 (p*t) t}

def signedSweep (κ k : ℝ) : Set Space :=
  {z | ∃ s p t : ℝ, |s| ≤ 1 ∧ |p| ≤ 1 ∧ 0 ≤ t ∧ t ≤ height k p ∧
    z = vec3 s (p*t+s*κ*v p) (t+s*κ*w p)}

def apexSweep (κ ρ : ℝ) : Set Space :=
  {z | ∃ s p t : ℝ, |s| ≤ 1 ∧ |p| ≤ 1 ∧ 0 ≤ t ∧ t ≤ ρ ∧
    z = vec3 s (p*t+s*κ*v p) (t+s*κ*w p)}

end CylinderCovering.Nilpotent

end

end OAI
