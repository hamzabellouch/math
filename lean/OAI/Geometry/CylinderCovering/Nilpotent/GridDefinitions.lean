import OAI.Geometry.RuledCovering.Model

namespace OAI

noncomputable section
namespace NilpotentGrid
open Set
abbrev Plane := RuledApproximation.Plane

def coarseCell (δ : ℝ) (z : ℤ × ℤ) : Set Plane :=
  {x | δ * (z.1 : ℝ) ≤ x 0 ∧ x 0 ≤ δ * ((z.1 : ℝ) + 1) ∧
       δ * (z.2 : ℝ) ≤ x 1 ∧ x 1 ≤ δ * ((z.2 : ℝ) + 1)}

def gridBound (δ B : ℝ) : ℤ := ⌈B / δ⌉

def indexRange (δ B : ℝ) : Finset ℤ :=
  Finset.Icc (-gridBound δ B - 1) (gridBound δ B)

def candidates (δ B : ℝ) : Finset (ℤ × ℤ) :=
  (indexRange δ B).product (indexRange δ B)

def coarseIndices (δ B : ℝ) (D : Set Plane) : Finset (ℤ × ℤ) := by
  classical
  exact (candidates δ B).filter (fun z => (D ∩ coarseCell δ z).Nonempty)

def coarseUnion (δ B : ℝ) (D : Set Plane) : Set Plane :=
  ⋃ z ∈ coarseIndices δ B D, coarseCell δ z

end NilpotentGrid

end

end OAI
