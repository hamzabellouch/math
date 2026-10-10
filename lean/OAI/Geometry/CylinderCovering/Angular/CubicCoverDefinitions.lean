import OAI.Geometry.TriangularCovering.Basic
import OAI.Geometry.CylinderCovering.Angular.MarginsDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.Cubic
open Set TriangularCovering

def K4 : Set Space :=
  {p | ∃ x y z : ℝ, -1 ≤ z ∧ z ≤ 1 ∧ |x| ≤ 1 - z ∧ |y| ≤ 1 + z ∧
    p = point x y z}

def CoversK4 {m : ℕ} (c : Fin m → TriCylinder) : Prop :=
  ∀ p ∈ K4, ∃ i : Fin m, p ∈ (c i).carrier

def cubicCost (ε : ℝ) : ℝ :=
  H * ∑ j : Fin (n ε),
    step (n ε) * cap ε (node (n ε) j) (node (n ε) (j + 1)) ^ 2 /
      Real.sqrt (1 + ε ^ 2 *
        (alpha (node (n ε) j) (node (n ε) (j + 1)) ^ 2 +
          2 * beta (node (n ε) j) (node (n ε) (j + 1)) ^ 2))

def lowerDirection (ε a b : ℝ) : Space :=
  !₂[1, ε * alpha a b, H * ε * beta a b]

def upperDirection (ε a b : ℝ) : Space :=
  !₂[-ε * alpha a b, 1, H * ε * beta a b]

def normalizedDirection (v : Space) : Space := ‖v‖⁻¹ • v

def lowerInterceptVertices (ε a b : ℝ) : Fin 3 → Space :=
  ![point 0 0 (-1), point 0 (a * cap ε a b) (cap ε a b - 1),
    point 0 (b * cap ε a b) (cap ε a b - 1)]

def upperInterceptVertices (ε a b : ℝ) : Fin 3 → Space :=
  ![point 0 0 1, point (a * cap ε a b) 0 (1 - cap ε a b),
    point (b * cap ε a b) 0 (1 - cap ε a b)]

def lowerIndex (ε : ℝ) (j : Fin (n ε)) : Fin (2 * n ε) :=
  Fin.cast (two_mul (n ε)).symm (Fin.castAdd (n ε) j)

def upperIndex (ε : ℝ) (j : Fin (n ε)) : Fin (2 * n ε) :=
  Fin.cast (two_mul (n ε)).symm (Fin.natAdd (n ε) j)

def PrescribedFamily (ε : ℝ) (c : Fin (2 * n ε) → TriCylinder) : Prop :=
  ∀ j : Fin (n ε),
    let a := node (n ε) j
    let b := node (n ε) (j + 1)
    (c (lowerIndex ε j)).axis = normalizedDirection (lowerDirection ε a b) ∧
    (c (lowerIndex ε j)).base = projection (normalizedDirection (lowerDirection ε a b)) ''
      convexHull ℝ (Set.range (lowerInterceptVertices ε a b)) ∧
    (c (upperIndex ε j)).axis = normalizedDirection (upperDirection ε a b) ∧
    (c (upperIndex ε j)).base = projection (normalizedDirection (upperDirection ε a b)) ''
      convexHull ℝ (Set.range (upperInterceptVertices ε a b))

def FiniteCoverStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
    ∃ c : Fin (2 * n ε) → TriCylinder, CoversK4 c ∧ totalArea c = cubicCost ε ∧ PrescribedFamily ε c

def minimumProjection4 : ℝ :=
  sInf {a : ℝ | ∃ u : Space, ‖u‖ = 1 ∧ a = area (projection u '' K4)}

def relativeCost4 {m : ℕ} (c : Fin m → TriCylinder) : ℝ :=
  ∑ i : Fin m, area (c i).base / area (projection (c i).axis '' K4)

def MainStatement : Prop :=
  minimumProjection4 = 4 * H ∧
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ c : Fin (2 * n ε) → TriCylinder,
        CoversK4 c ∧ PrescribedFamily ε c ∧ totalArea c = cubicCost ε ∧
        |totalArea c - (2 * H - H / 15 * ε ^ 2)| ≤ C * ε ^ 3 ∧
        (ε < δ → totalArea c < minimumProjection4 / 2)

def scaledLowerInterceptVertices (ε a b : ℝ) : Fin 3 → Space :=
  ![point 0 0 0, point 0 (a * (cap ε a b / 2)) (cap ε a b / 2),
    point 0 (b * (cap ε a b / 2)) (cap ε a b / 2)]

def scaledUpperInterceptVertices (ε a b : ℝ) : Fin 3 → Space :=
  ![point 0 0 1, point (a * (cap ε a b / 2)) 0 (1 - cap ε a b / 2),
    point (b * (cap ε a b / 2)) 0 (1 - cap ε a b / 2)]

def lowerIndexN (N : ℕ) (j : Fin N) : Fin (2 * N) :=
  Fin.cast (two_mul N).symm (Fin.castAdd N j)

def upperIndexN (N : ℕ) (j : Fin N) : Fin (2 * N) :=
  Fin.cast (two_mul N).symm (Fin.natAdd N j)

def ScaledPrescribedFamily (ε : ℝ) (N : ℕ) (c : Fin (2 * N) → TriCylinder) : Prop :=
  ∀ j : Fin N,
    let a := node N j
    let b := node N (j + 1)
    (c (lowerIndexN N j)).axis = normalizedDirection (lowerDirection ε a b) ∧
    (c (lowerIndexN N j)).base = projection (normalizedDirection (lowerDirection ε a b)) ''
      convexHull ℝ (Set.range (scaledLowerInterceptVertices ε a b)) ∧
    (c (upperIndexN N j)).axis = normalizedDirection (upperDirection ε a b) ∧
    (c (upperIndexN N j)).base = projection (normalizedDirection (upperDirection ε a b)) ''
      convexHull ℝ (Set.range (scaledUpperInterceptVertices ε a b))

def ScaledFiniteCoverStatement : Prop :=
  ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
    ∃ c : Fin (2 * ⌈8 / τ ^ 2⌉₊) → TriCylinder,
      Covers c ∧ totalArea c = cubicCost (τ / 2) / 4 ∧
      ScaledPrescribedFamily (τ / 2) ⌈8 / τ ^ 2⌉₊ c

def ScaledMainStatement : Prop :=
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
    ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∃ c : Fin (2 * ⌈8 / τ ^ 2⌉₊) → TriCylinder,
        Covers c ∧ ScaledPrescribedFamily (τ / 2) ⌈8 / τ ^ 2⌉₊ c ∧
        totalArea c = cubicCost (τ / 2) / 4 ∧
        |totalArea c / H - (1 / 2 - τ ^ 2 / 240)| ≤ C * τ ^ 3 ∧
        (τ < δ → totalArea c < A_min / 2)

end CylinderCovering.Cubic

end

end OAI
