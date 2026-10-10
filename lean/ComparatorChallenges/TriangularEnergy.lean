import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal
open Classical Filter

namespace TriangularUniversal

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def LocallyFinite (C : Set Plane) : Prop :=
  ∀ R : ℝ, (C ∩ Metric.closedBall (0 : Plane) R).Finite

def diskPoints (C : Set Plane) (R : ℝ) : Finset Plane :=
  if h : (C ∩ Metric.closedBall (0 : Plane) R).Finite then h.toFinset else ∅

def diskCount (C : Set Plane) (R : ℝ) : ℕ := (diskPoints C R).card

def DensityOne (C : Set Plane) : Prop :=
  Tendsto (fun R : ℝ => (diskCount C R : ℝ) / (Real.pi * R ^ 2))
    atTop (𝓝 1)

def AdmissiblePotential (g : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) g (Set.Ioi 0) ∧
  (∀ t : ℝ, 0 < t → 0 ≤ g t) ∧
  ∀ (r : ℕ) (t : ℝ), 0 < t → 0 ≤ (-1 : ℝ) ^ r * iteratedDeriv r g t

def diskEnergy (g : ℝ → ℝ) (C : Set Plane) (R : ℝ) : ℝ≥0∞ :=
  (diskCount C R : ℝ≥0∞)⁻¹ *
    ∑ x ∈ diskPoints C R, ∑ y ∈ (diskPoints C R).erase x,
      ENNReal.ofReal (g (‖x - y‖ ^ 2))

def energy (g : ℝ → ℝ) (C : Set Plane) : ℝ≥0∞ :=
  Filter.liminf (diskEnergy g C) atTop

end TriangularUniversal

namespace AtomicTriangular

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def b : ℝ := Real.sqrt 3 / 2

def triangularPoint (jk : ℤ × ℤ) : Plane :=
  (Real.sqrt b)⁻¹ •
    (EuclideanSpace.single 0 ((jk.1 : ℝ) + (jk.2 : ℝ) / 2) +
      EuclideanSpace.single 1 ((jk.2 : ℝ) * b))

def A : Set Plane := Set.range triangularPoint

abbrev LocallyFinite := TriangularUniversal.LocallyFinite
abbrev diskPoints := TriangularUniversal.diskPoints
abbrev diskCount := TriangularUniversal.diskCount
abbrev DensityOne := TriangularUniversal.DensityOne
abbrev AdmissiblePotential := TriangularUniversal.AdmissiblePotential
abbrev diskEnergy := TriangularUniversal.diskEnergy
abbrev energy := TriangularUniversal.energy

/-- The full nonzero-lattice energy, allowing a divergent series. -/
def latticeEnergy (g : ℝ → ℝ) : ℝ≥0∞ :=
  ∑' a : {x : Plane // x ∈ A ∧ x ≠ 0}, ENNReal.ofReal (g (‖a.val‖ ^ 2))

/-- Universal energy minimality for smooth completely monotone potentials, with attainment. -/
theorem universal_energy_minimum (g : ℝ → ℝ) (C : Set Plane)
    (hg : AdmissiblePotential g) (hC : LocallyFinite C) (hd : DensityOne C) :
    latticeEnergy g ≤ energy g C ∧ latticeEnergy g = energy g A := by
  sorry

end AtomicTriangular
end

end OAI
