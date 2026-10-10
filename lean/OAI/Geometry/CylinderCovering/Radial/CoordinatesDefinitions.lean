import Mathlib

namespace OAI

noncomputable section

namespace RadialCoordinates

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev BarycentricSpace := EuclideanSpace ℝ (Fin 4)

def barycentricSimplex : Set BarycentricSpace :=
  {z | (∀ i, 0 ≤ z i) ∧ ∑ i, z i = 1}

def barycentricPoint (s q p : ℝ) : BarycentricSpace :=
  !₂[(s + q) / 2, (s - q) / 2, (1 - s + p) / 2, (1 - s - p) / 2]

def canonicalPoint (s q p : ℝ) : Space :=
  !₂[2 * q, 2 * p, Real.sqrt 2 * (2 * s - 1)]

def canonicalTetrahedron : Set Space :=
  {z | ∃ X Y Z : ℝ, -1 ≤ Z ∧ Z ≤ 1 ∧ |X| ≤ 1 + Z ∧
      |Y| ≤ 1 - Z ∧ z = !₂[X, Y, Real.sqrt 2 * Z]}

def angular (t : ℝ) : ℝ := 2 * t - 1

def velocity (t : ℝ) : Plane := !₂[t ^ 2, -(1 - t) ^ 2]

def ray (t : ℝ) : Plane := !₂[t, 1 - t]

def capPolynomial (v : ℝ) : ℝ := v ^ 2 + 4 * v ^ 4 + 1 / 1000

def cap (k t : ℝ) : ℝ := 1 / 2 + k ^ 2 * capPolynomial (angular t / 2)

def speedSquared (t : ℝ) : ℝ :=
  2 * angular t ^ 2 + (t ^ 2 + (1 - t) ^ 2) ^ 2

def firstSweepImagePoint (k S t p : ℝ) : BarycentricSpace :=
  barycentricPoint (S + k * p * angular t)
    (S * angular t + k * p * (t ^ 2 + (1 - t) ^ 2)) p

def secondSweepImagePoint (k T r q : ℝ) : BarycentricSpace :=
  barycentricPoint (1 - T + k * q * angular r) q
    (T * angular r - k * q * (r ^ 2 + (1 - r) ^ 2))

def firstSweepImage (k : ℝ) : Set BarycentricSpace :=
  {v | ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ S ∈ Set.Icc (0 : ℝ) (cap k t),
      ∃ p ∈ Set.Icc (-1 : ℝ) 1, v = firstSweepImagePoint k S t p}

def secondSweepImage (k : ℝ) : Set BarycentricSpace :=
  {v | ∃ r ∈ Set.Icc (0 : ℝ) 1, ∃ T ∈ Set.Icc (0 : ℝ) (cap k r),
      ∃ q ∈ Set.Icc (-1 : ℝ) 1, v = secondSweepImagePoint k T r q}

def J (k : ℝ) : ℝ := Real.sqrt 2 *
  ∫ t in (0 : ℝ)..1, (cap k t) ^ 2 / (2 * Real.sqrt (1 + k ^ 2 * speedSquared t))

def interceptTangentA : BarycentricSpace := !₂[1, 0, -1 / 2, -1 / 2]

def interceptTangentB : BarycentricSpace := !₂[0, 1, -1 / 2, -1 / 2]

def interceptNormal : BarycentricSpace := !₂[0, 0, 1 / Real.sqrt 2, -1 / Real.sqrt 2]

def firstDirection (k t : ℝ) : BarycentricSpace :=
  !₂[k * t ^ 2, -k * (1 - t) ^ 2,
    (1 - k * angular t) / 2, (-1 - k * angular t) / 2]

end RadialCoordinates

end

end OAI
