import Mathlib

namespace OAI

noncomputable section

namespace AngularCaps

def d (q : ℝ) : ℝ := (q ^ 2 + q ^ 4) / 16

def squaredRadius (τ η q : ℝ) : ℝ :=
  Real.sqrt (1 / 4 + τ ^ 2 * (d q + η))

def radialParameterSet (l r : ℝ) (R : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.Icc l r ∧ p.2 ∈ Set.Icc 0 (R p.1)}

def radialMap (p : ℝ × ℝ) : ℝ × ℝ := (p.1 * p.2, p.2)

def radialSector (l r : ℝ) (R : ℝ → ℝ) : Set (ℝ × ℝ) :=
  radialMap '' radialParameterSet l r R

def radialBandParameters (l r ρ : ℝ) (R : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.Icc l r ∧ p.2 ∈ Set.Icc ρ (R p.1)}

def radialBand (l r ρ : ℝ) (R : ℝ → ℝ) : Set (ℝ × ℝ) :=
  radialMap '' radialBandParameters l r ρ R

def pairToPlane (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) := !₂[p.1, p.2]

def euclideanRadialSector (l r : ℝ) (R : ℝ → ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  pairToPlane '' radialSector l r R

def euclideanRadialBand (l r ρ : ℝ) (R : ℝ → ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  pairToPlane '' radialBand l r ρ R

end AngularCaps

end

end OAI
