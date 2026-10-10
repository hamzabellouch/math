import OAI.Geometry.IsometricImmersion.Calculus.CoordinateDerivatives
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace OAI

noncomputable section
open scoped BigOperators Matrix ContDiff
namespace SmoothLocal.Geometry

abbrev Ambient := EuclideanSpace ℝ (Fin 3)
abbrev MetricField := Coord → Matrix (Fin 2) (Fin 2) ℝ

def square : Set Coord := {p | ∀ i, p i ∈ Set.Ioo (-1 : ℝ) 1}

def SmoothPositiveOn (g : MetricField) (U : Set Coord) : Prop :=
  (∀ i j, ContDiffOn ℝ ∞ (fun p => g p i j) U) ∧ ∀ p ∈ U, (g p).PosDef

def IsometricOn (g : MetricField) (F : Coord → Ambient) (U : Set Coord) : Prop :=
  ContDiffOn ℝ ∞ F U ∧ ∀ p ∈ U, ∀ v w : Coord,
    inner ℝ (fderiv ℝ F p v) (fderiv ℝ F p w) = v ⬝ᵥ (g p *ᵥ w)

def inverseMetric (g : MetricField) (p : Coord) := (g p)⁻¹

def christoffel (g : MetricField) (k i j : Fin 2) (p : Coord) : ℝ :=
  (1 / 2 : ℝ) * ∑ l, inverseMetric g p k l *
    (coordPartial i (fun q => g q j l) p + coordPartial j (fun q => g q i l) p -
      coordPartial l (fun q => g q i j) p)

def covHessian (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  coordPartial i (coordPartial j z) p - ∑ k, christoffel g k i j p * coordPartial k z p

def covectorNormSq (g : MetricField) (z : Coord → ℝ) (p : Coord) : ℝ :=
  ∑ i, ∑ j, inverseMetric g p i j * coordPartial i z p * coordPartial j z p

def riemann (g : MetricField) (l k i j : Fin 2) (p : Coord) : ℝ :=
  coordPartial i (christoffel g l j k) p - coordPartial j (christoffel g l i k) p +
    ∑ m, (christoffel g m j k p * christoffel g l i m p -
      christoffel g m i k p * christoffel g l j m p)

def gaussianCurvature (g : MetricField) (p : Coord) : ℝ :=
  (∑ l, g p 0 l * riemann g l 1 0 1 p) / (g p).det

def height (F : Coord → Ambient) (e : Ambient) : Coord → ℝ :=
  fun p => inner ℝ (F p) e

def secondFundamental (F : Coord → Ambient) (n : Ambient) (p : Coord) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => inner ℝ (coordPartial i (coordPartial j F) p) n

theorem isometricOn_injective_differential {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    {p : Coord} (hp : p ∈ U) : Function.Injective (fderiv ℝ F p) := by
  intro v w hvw
  have hL : fderiv ℝ F p (v - w) = 0 := by simp [map_sub, hvw]
  have hv : v - w = 0 := by
    by_contra hne
    have hpos := (hg.2 p hp).dotProduct_mulVec_pos hne
    have heq := hF.2 p hp (v - w) (v - w)
    rw [hL, inner_zero_left] at heq
    have hpos' : 0 < (v - w) ⬝ᵥ (g p *ᵥ (v - w)) := by simpa using hpos
    exact (ne_of_gt hpos') heq.symm
  exact sub_eq_zero.mp hv

def MainTarget : Prop :=
  ∃ g : MetricField, SmoothPositiveOn g square ∧
    ∀ U : Set Coord, IsOpen U → U ⊆ square → (0 : Coord) ∈ U →
      ∀ F : Coord → Ambient, ¬ IsometricOn g F U

end SmoothLocal.Geometry

end

end OAI
