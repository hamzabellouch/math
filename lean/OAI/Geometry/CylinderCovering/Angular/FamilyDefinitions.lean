import OAI.Geometry.TriangularCovering.Basic

namespace OAI

noncomputable section
open Set

namespace TriangularCovering.AngularFamily

def LowerHit (ε a b A B R x y t : ℝ) : Prop :=
  0 ≤ t - ε*x*B ∧ t - ε*x*B ≤ R ∧
    a*(t - ε*x*B) ≤ y - ε*x*A ∧ y - ε*x*A ≤ b*(t - ε*x*B)

def UpperHit (ε a b A B R x y t : ℝ) : Prop :=
  0 ≤ 1 - t + ε*y*B ∧ 1 - t + ε*y*B ≤ R ∧
    a*(1 - t + ε*y*B) ≤ x + ε*y*A ∧ x + ε*y*A ≤ b*(1 - t + ε*y*B)

def lowerDirection (ε A B : ℝ) : Space := !₂[1, ε*A, H*ε*B]
def upperDirection (ε A B : ℝ) : Space := !₂[-ε*A, 1, H*ε*B]

def lowerIntercept (a b R : ℝ) : Set Space :=
  convexHull ℝ (range (![point 0 0 0, point 0 (a*R) R, point 0 (b*R) R] : Fin 3 → Space))

def upperIntercept (a b R : ℝ) : Set Space :=
  convexHull ℝ (range (![point 0 0 1, point (a*R) 0 (1-R), point (b*R) 0 (1-R)] : Fin 3 → Space))

def PrescribedLower (C : TriCylinder) (ε a b A B R : ℝ) : Prop :=
  C.axis = ‖lowerDirection ε A B‖⁻¹ • lowerDirection ε A B ∧
    C.base = projection C.axis '' lowerIntercept a b R

def PrescribedUpper (C : TriCylinder) (ε a b A B R : ℝ) : Prop :=
  C.axis = ‖upperDirection ε A B‖⁻¹ • upperDirection ε A B ∧
    C.base = projection C.axis '' upperIntercept a b R

def PrescribedFamily {n : ℕ} (C : Fin (2*n) → TriCylinder)
    (ε : ℝ) (a b A B R : Fin n → ℝ) : Prop :=
  (∀ j : Fin n, PrescribedLower
    (C (Fin.cast (two_mul n).symm (Fin.castAdd n j))) ε (a j) (b j) (A j) (B j) (R j)) ∧
  (∀ j : Fin n, PrescribedUpper
    (C (Fin.cast (two_mul n).symm (Fin.natAdd n j))) ε (a j) (b j) (A j) (B j) (R j))

end TriangularCovering.AngularFamily

end

end OAI
