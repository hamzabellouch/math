import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

namespace Invariant233.ScalarEndpointDensity
noncomputable section

def cutDistance (z : ℝ) : ℝ := min z (1 - z)

def endpointMap (t z : ℝ) : ℝ := z + t * cutDistance z

def midpoint (t : ℝ) : ℝ := (1 + t) / 2

def slopeDensity (t s : ℝ) : ℝ :=
  if s ≤ midpoint t then (1 + t)⁻¹ else (1 - t)⁻¹

def averagedDensity (h s : ℝ) : ℝ :=
  h⁻¹ * ∫ t in (0 : ℝ)..h, slopeDensity t s

end

end Invariant233.ScalarEndpointDensity

end OAI
