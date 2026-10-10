import Mathlib

namespace OAI

noncomputable section
namespace AngularTable

structure Parameters where
  edge : ℝ
  tilt : ℝ
  margin : ℝ
  sectors : ℕ

def quadraticCost (p : Parameters) : ℝ :=
  1 / 2 + (2 * p.margin - 1 / 240) * p.tilt ^ 2

def mesh (p : Parameters) : ℝ := 2 / p.sectors

def midpointFour (n : ℕ) : Parameters := ⟨4, 2 / n, 1 / 1920, 2 * n ^ 2⟩

def midpointOne (α : ℝ) : Parameters := ⟨1, α, 1 / 1000, ⌈(α⁻¹) ^ 2⌉₊⟩

def midpointTwo (n : ℕ) : Parameters := ⟨2, 1 / n, 1 / 1000, n ^ 2⟩

def continuousTwo (c : ℝ) (m : ℕ) : Parameters := ⟨2, c, 1 / 1000, m⟩

def squaredTwo (n : ℕ) : Parameters := ⟨2, 2 / n, 1 / 960, n ^ 2⟩

def maximumOne (n : ℕ) : Parameters := ⟨1, 1 / (4 * n), 1 / 960, n ^ 2⟩

def cartesianThreeQuarters (t : ℝ) : Parameters :=
  ⟨Real.sqrt 2, t / 2, 1 / 960, ⌈Real.sqrt 2 / t ^ 2⌉₊⟩

def cartesianOne (n : ℕ) : Parameters := ⟨1, 1 / (2 * n), 1 / 1000, n ^ 2⟩

end AngularTable

end

end OAI
