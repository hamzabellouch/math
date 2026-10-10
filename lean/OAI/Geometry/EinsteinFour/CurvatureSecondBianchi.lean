import OAI.Geometry.EinsteinFour.CurvatureFirstBianchi
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace OAI

/-! The coordinate second Bianchi identity. The matrix algebra separates
the commuting second derivatives from the Jacobi cancellation. -/

namespace PositiveEinsteinFour.CovariantBianchi

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

abbrev Mat := Matrix (Fin 4) (Fin 4) ℝ

def curvature (C : Fin 4 → Mat) (D : Fin 4 → Fin 4 → Mat) (i j : Fin 4) : Mat :=
  D i j - D j i + C i * C j - C j * C i

theorem curvature_skew (C : Fin 4 → Mat) (D : Fin 4 → Fin 4 → Mat) (i j : Fin 4) :
    curvature C D i j = -curvature C D j i := by
  unfold curvature
  noncomm_ring

def curvatureDerivative (C : Fin 4 → Mat) (D : Fin 4 → Fin 4 → Mat)
    (E : Fin 4 → Fin 4 → Fin 4 → Mat) (i j k : Fin 4) : Mat :=
  E i j k - E i k j + D i j * C k + C j * D i k - D i k * C j - C k * D i j

def covariantCurvatureDerivative (C : Fin 4 → Mat) (D : Fin 4 → Fin 4 → Mat)
    (E : Fin 4 → Fin 4 → Fin 4 → Mat) (i j k : Fin 4) : Mat :=
  curvatureDerivative C D E i j k + C i * curvature C D j k - curvature C D j k * C i

theorem cyclic_identity_of_commuting_derivatives
    (C : Fin 4 → Mat) (D : Fin 4 → Fin 4 → Mat)
    (E : Fin 4 → Fin 4 → Fin 4 → Mat)
    (hE : ∀ i j k, E i j k = E j i k) (i j k : Fin 4) :
    covariantCurvatureDerivative C D E i j k +
      covariantCurvatureDerivative C D E j k i +
      covariantCurvatureDerivative C D E k i j = 0 := by
  unfold covariantCurvatureDerivative curvatureDerivative curvature
  rw [hE j i k, hE k i j, hE k j i]
  noncomm_ring

def lowerSlotCorrection (C : Fin 4 → Mat) (D : Fin 4 → Fin 4 → Mat)
    (i j k : Fin 4) : Mat :=
  ∑ p, (C i p j • curvature C D p k + C i p k • curvature C D j p)

theorem lowerSlotCorrection_cyclic
    (C : Fin 4 → Mat) (D : Fin 4 → Fin 4 → Mat)
    (hC : ∀ i j p, C i p j = C j p i) (i j k : Fin 4) :
    lowerSlotCorrection C D i j k + lowerSlotCorrection C D j k i +
      lowerSlotCorrection C D k i j = 0 := by
  unfold lowerSlotCorrection
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro p _
  rw [hC j i p, hC k i p, hC k j p,
    curvature_skew C D p i, curvature_skew C D k p, curvature_skew C D p j]
  module

def tensorCurvatureDerivative (C : Fin 4 → Mat) (D : Fin 4 → Fin 4 → Mat)
    (E : Fin 4 → Fin 4 → Fin 4 → Mat) (i j k : Fin 4) : Mat :=
  covariantCurvatureDerivative C D E i j k - lowerSlotCorrection C D i j k

theorem tensorCurvatureDerivative_cyclic
    (C : Fin 4 → Mat) (D : Fin 4 → Fin 4 → Mat)
    (E : Fin 4 → Fin 4 → Fin 4 → Mat)
    (hC : ∀ i j p, C i p j = C j p i)
    (hE : ∀ i j k, E i j k = E j i k) (i j k : Fin 4) :
    tensorCurvatureDerivative C D E i j k +
      tensorCurvatureDerivative C D E j k i +
      tensorCurvatureDerivative C D E k i j = 0 := by
  have hc := cyclic_identity_of_commuting_derivatives C D E hE i j k
  have hl := lowerSlotCorrection_cyclic C D hC i j k
  unfold tensorCurvatureDerivative
  calc
    _ = (covariantCurvatureDerivative C D E i j k +
        covariantCurvatureDerivative C D E j k i +
        covariantCurvatureDerivative C D E k i j) -
        (lowerSlotCorrection C D i j k + lowerSlotCorrection C D j k i +
        lowerSlotCorrection C D k i j) := by abel
    _ = 0 := by rw [hc, hl]; simp

end
end PositiveEinsteinFour.CovariantBianchi

end OAI
