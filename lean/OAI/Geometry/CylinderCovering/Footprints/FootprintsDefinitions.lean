import Mathlib

namespace OAI

namespace RadialFootprints

def absoluteFootprint (A B M d m : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.Icc (-A * d) (M + A * d) ∧
    |p.2 - m * p.1| ≤ d / 2 * |p.1| + B * d ^ 2}

def affineFootprint (A B M d m : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.Icc (-A * d) (M + A * d) ∧
    |p.2 - m * p.1| ≤ d / 2 * p.1 + B * d ^ 2}

def halfheightFootprint (ρ e M m : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.Icc (-e) (M + e) ∧
    |p.2 - m * p.1| ≤ ρ * (p.1 + 2 * e)}

end RadialFootprints

end OAI
