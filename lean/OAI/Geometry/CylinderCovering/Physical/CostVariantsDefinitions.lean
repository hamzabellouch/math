import OAI.Geometry.CylinderCovering.Physical.CoordinatesDefinitions
import OAI.Geometry.CylinderCovering.Radial.CapsDefinitions

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace RadialPhysical

def RelativeCostExpansion (f : ℝ → ℝ) (reference coefficient : ℝ) : Prop :=
  (fun τ => f τ - reference * (1 + coefficient * τ ^ 2))
    =O[𝓝[>] (0 : ℝ)] (fun τ => τ ^ 4)

def PhysicalCostTableStatement : Prop :=
  RelativeCostExpansion (fun τ => scaledCost 1 τ (linearCap 1 τ (1/120)))
    (height 1 / 2) (-1/60) ∧
  RelativeCostExpansion (fun τ => scaledCost (1/2) (τ/2) (linearCap (1/2) (τ/2) (1/120)))
    (height (1/2) / 4) (-1/3840) ∧
  RelativeCostExpansion (fun τ => scaledCost (1/Real.sqrt 2) τ
    (linearCap (1/Real.sqrt 2) τ (1/125)))
    ((1/Real.sqrt 2) * height (1/Real.sqrt 2) / 2) (-13/3000) ∧
  RelativeCostExpansion (fun τ => scaledCost (1/Real.sqrt 2) τ
    (squareCap (1/Real.sqrt 2) τ (1/125)))
    ((1/Real.sqrt 2) * height (1/Real.sqrt 2) / 2) (-13/3000) ∧
  RelativeCostExpansion (fun τ => scaledCost (1/2) τ (linearCap (1/2) τ (4/625)))
    (height (1/2) / 4) (-77/60000) ∧
  RelativeCostExpansion (fun τ => scaledCost (1/2) (2*τ) (squareCap (1/2) (2*τ) (1/120)))
    (height (1/2) / 4) (-1/240) ∧
  RelativeCostExpansion (fun τ => scaledCost 1 (2*τ) (linearCap 1 (2*τ) (1/200)))
    (height 1 / 2) (-7/75)

def centeredFractionalCap (b η s : ℝ) : ℝ :=
  1 + η ^ 2 * s ^ 2 * (b ^ 2 + s ^ 2) / 2 + η ^ (5/2 : ℝ)

def nonorthCost (ε : ℝ) (R : ℝ → ℝ) : ℝ :=
  scaledCost (1/Real.sqrt 2) (2*ε) (fun s => R (Real.sqrt 2 * s))

structure PhysicalCostVariantsStatement : Prop where
  linearExpansion : ∀ b β a : ℝ, 0 < b → 0 ≤ β →
    (fun τ => scaledCost b (a*τ) (linearCap b (a*τ) β) - quadraticCost b (a*τ) β)
      =O[𝓝[>] (0:ℝ)] (fun τ => τ^4)
  squareExpansion : ∀ b β a : ℝ, 0 < b → 0 ≤ β →
    (fun τ => scaledCost b (a*τ) (squareCap b (a*τ) β) - quadraticCost b (a*τ) β)
      =O[𝓝[>] (0:ℝ)] (fun τ => τ^4)
  linearSaving : ∀ b β : ℝ, 0 < b → 0 < β → β < 1/60 →
    ∀ᶠ η : ℝ in 𝓝[>] 0, scaledCost b η (linearCap b η β) < b*height b/2
  squareSaving : ∀ b β : ℝ, 0 < b → 0 < β → β < 1/60 →
    ∀ᶠ η : ℝ in 𝓝[>] 0, scaledCost b η (squareCap b η β) < b*height b/2
  table : PhysicalCostTableStatement
  centeredLinearExpansion : ∀ b β a : ℝ, 0 < b → 0 ≤ β →
    (fun τ => scaledCost b (a*τ) (centeredLinearCap b (a*τ) β) -
      2*b*height b*(1+relativeQuadraticTerm b (a*τ) β))
      =O[𝓝[>] (0:ℝ)] (fun τ => τ^4)
  centeredLinearSaving : ∀ b β : ℝ, 0 < b → 0 < β → β < 1/60 →
    ∀ᶠ η : ℝ in 𝓝[>] 0, scaledCost b η (centeredLinearCap b η β) < 2*b*height b
  centeredFractionalDictionary : ∀ η : ℝ, 0 < η → ∀ r : ℝ,
    centeredFractionalCap (1/Real.sqrt 2) η ((1/Real.sqrt 2)*r) =
      CylinderCovering.RadialCaps.fractionalCap (4*Real.sqrt 2) (η/2) r
  centeredFractionalExpansion :
    (fun η => scaledCost (1/Real.sqrt 2) η (centeredFractionalCap (1/Real.sqrt 2) η) -
      (1/Real.sqrt 2)*(2-η^2/60+4*η^(5/2:ℝ)))
      =O[𝓝[>] (0:ℝ)] (fun η => η^4)
  centeredFractionalLittleO :
    (fun η => scaledCost (1/Real.sqrt 2) η (centeredFractionalCap (1/Real.sqrt 2) η) -
      (1/Real.sqrt 2)*(2-η^2/60)) =o[𝓝[>] (0:ℝ)] (fun η => η^2)
  centeredFractionalSaving :
    ∀ᶠ η : ℝ in 𝓝[>] 0, scaledCost (1/Real.sqrt 2) η
      (centeredFractionalCap (1/Real.sqrt 2) η) < 2/Real.sqrt 2
  nonorthDictionary : ∀ ε : ℝ, ∀ R : ℝ → ℝ,
    nonorthCost ε R = Real.sqrt 2 * CylinderCovering.RadialCaps.Q R ε
  nonorthCubic :
    (fun ε => nonorthCost ε (CylinderCovering.RadialCaps.cubicCap 5 ε) -
      Real.sqrt 2*(1-ε^2/30+10*ε^3)) =O[𝓝[>] (0:ℝ)] (fun ε => ε^4)
  nonorthFractional :
    (fun ε => nonorthCost ε (CylinderCovering.RadialCaps.fractionalCap 1 ε) -
      Real.sqrt 2*(1-ε^2/30+2*ε^(5/2:ℝ))) =O[𝓝[>] (0:ℝ)] (fun ε => ε^4)
end RadialPhysical

end

end OAI
