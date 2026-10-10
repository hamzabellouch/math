import OAI.Geometry.CylinderCovering.Nilpotent.BasicDefinitions

namespace OAI

open Set MeasureTheory

noncomputable section
namespace CylinderCovering.NilpotentApexNet

def meshCount (ρ : ℝ) : ℕ := ⌈2 / ρ⌉₊

def node (ρ : ℝ) (j : ℕ) : ℝ := -1 + 2 * j / meshCount ρ

def velocity (k σ p : ℝ) : ℝ × ℝ :=
  (σ * k * Nilpotent.v p, σ * k * Nilpotent.w p)

def radius (k ρ : ℝ) : ℝ := (1 + k / 2) * ρ

def tile (k ρ : ℝ) : Set (ℝ × ℝ) :=
  Icc (-radius k ρ, -radius k ρ) (radius k ρ, radius k ρ)

def cylinder (k ρ σ : ℝ) (j : Fin (meshCount ρ + 1)) : Set (ℝ × (ℝ × ℝ)) :=
  {z | z.2 - z.1 • velocity k σ (node ρ j) ∈ tile k ρ}

def apexSweep (k ρ σ : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  {z | ∃ s p t : ℝ, |s| ≤ 1 ∧ |p| ≤ 1 ∧ 0 ≤ t ∧ t ≤ ρ ∧
    z = (s, (p * t, t) + s • velocity k σ p)}

def weight (h : ℝ) (g : ℝ × ℝ) : ℝ :=
  1 / Real.sqrt (1 + g.1 ^ 2 + h ^ 2 * g.2 ^ 2)

def weightedArea (h k ρ σ : ℝ) (j : Fin (meshCount ρ + 1)) : ℝ :=
  (volume (tile k ρ)).toReal * weight h (velocity k σ (node ρ j))

def AuxiliaryApexNetStatement : Prop :=
  ∀ (h k ρ σ : ℝ), 0 ≤ k → 0 < ρ → ρ ≤ 1 → |σ| ≤ 1 →
    IsCompact (tile k ρ) ∧ Convex ℝ (tile k ρ) ∧ MeasurableSet (tile k ρ) ∧
    0 < (volume (tile k ρ)).toReal ∧
    (volume (tile k ρ)).toReal = (2 * (1 + k / 2) * ρ) ^ 2 ∧
    (meshCount ρ + 1 : ℕ) ≤ (4 / ρ : ℝ) ∧
    apexSweep k ρ σ ⊆ ⋃ j : Fin (meshCount ρ + 1), cylinder k ρ σ j ∧
    (∑ j : Fin (meshCount ρ + 1), weightedArea h k ρ σ j) ≤
      16 * (1 + k / 2) ^ 2 * ρ

end CylinderCovering.NilpotentApexNet

end

end OAI
