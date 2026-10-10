import Mathlib

namespace OAI

namespace CriticalHoneycomb
open scoped ENNReal

abbrev Center := ℤ × ℤ × Bool

def up (i j : ℤ) : Center := (i, j, true)
def down (i j : ℤ) : Center := (i, j, false)

/-- Adjacency across a full triangular edge. -/
def Adj (v w : Center) : Prop :=
  if v.2.2 then
    w.2.2 = false ∧ ((w.1 = v.1 ∧ w.2.1 = v.2.1) ∨
      (w.1 = v.1 ∧ w.2.1 = v.2.1 - 1) ∨
      (w.1 = v.1 - 1 ∧ w.2.1 = v.2.1))
  else
    w.2.2 = true ∧ ((w.1 = v.1 ∧ w.2.1 = v.2.1) ∨
      (w.1 = v.1 ∧ w.2.1 = v.2.1 + 1) ∨
      (w.1 = v.1 + 1 ∧ w.2.1 = v.2.1))

noncomputable def rowSpacing : ℝ := Real.sqrt 3 / 2

/-- The fixed Euclidean embedding in the unit triangular tiling. -/
noncomputable def centerPosition (v : Center) : ℝ × ℝ :=
  if v.2.2 then
    ((v.1 : ℝ) + (v.2.1 : ℝ) / 2 + 1 / 2,
      rowSpacing * ((v.2.1 : ℝ) + 1 / 3))
  else
    ((v.1 : ℝ) + (v.2.1 : ℝ) / 2 + 1,
      rowSpacing * ((v.2.1 : ℝ) + 2 / 3))

/-- A midpoint port, oriented into the triangle domain. -/
structure Port (D : Set Center) where
  inside : Center
  outside : Center
  adjacent : Adj inside outside
  inside_mem : inside ∈ D
  outside_not_mem : outside ∉ D

noncomputable def Port.position {D : Set Center} (p : Port D) : ℝ × ℝ :=
  ((centerPosition p.inside).1 / 2 + (centerPosition p.outside).1 / 2,
    (centerPosition p.inside).2 / 2 + (centerPosition p.outside).2 / 2)

/-- A simple center trace, with no premature boundary exit. -/
def IsTrace (D : Set Center) (p : List Center) : Prop :=
  p.Nodup ∧ p.IsChain Adj ∧ ∀ v ∈ p, v ∈ D

noncomputable def kappa : ℝ := (2 + Real.sqrt 2) ^ (-(1 : ℝ) / 2)

/-- Length counts centers; the port half-edges contribute no factors. -/
noncomputable def weight (p : List Center) : ℝ≥0∞ :=
  ENNReal.ofReal (kappa ^ p.length)

/-- The source's strip and tilt-compatible terminal support. -/
def strip (h : ℕ) : Set Center := {v | 0 ≤ v.2.1 ∧ v.2.1 < (h : ℤ)}
def StrictBridge (h : ℕ) :=
  {p : List Center // IsTrace (strip h) p ∧ p.head? = some (up 0 0) ∧
    ∃ i : ℤ, p.getLast? = some (down i ((h : ℤ) - 1))}
noncomputable def bridgeMass (h : ℕ) : ℝ≥0∞ :=
  if h = 0 then 1 else ∑' p : StrictBridge h, weight p.val

/-- Necessary estimate c:finite(1), inputs.tex:13, on the actual path sum. -/
def FiniteBridgeMassEstimate : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ h : ℕ,
    ENNReal.ofReal (c * (1 + (h : ℝ)) ^ (-(1 : ℝ) / 4)) ≤ bridgeMass h ∧
    bridgeMass h ≤ ENNReal.ofReal (C * (1 + (h : ℝ)) ^ (-(1 : ℝ) / 4))

/-- Trusted reference hole only; missing necessary main obligation. -/
theorem finiteBridgeMassEstimate : FiniteBridgeMassEstimate := by
  sorry

end CriticalHoneycomb


end OAI
