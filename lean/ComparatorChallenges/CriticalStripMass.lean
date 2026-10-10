import Mathlib

namespace OAI

 

namespace CriticalStrip

noncomputable section
open scoped BigOperators
open Set MeasureTheory

def rho : ℝ := 1 / Real.sqrt (2 + Real.sqrt 2)
def c : ℝ := Real.cos (3 * Real.pi / 8)
def lambda : ℝ := Real.pi / 8
def d : ℝ := Real.cos (2 * lambda)
def C : ℝ := Real.cos lambda
def eta : ℝ := 2 * d - 1

abbrev Triangle := ℤ × ℕ × Bool

def up (i : ℤ) (j : ℕ) : Triangle := (i, j, true)
def down (i : ℤ) (j : ℕ) : Triangle := (i, j, false)

def upDownAdjacent (v w : Triangle) : Prop :=
  v.2.2 = true ∧ w.2.2 = false ∧
    ((v.2.1 = w.2.1 ∧ (w.1 = v.1 ∨ w.1 + 1 = v.1)) ∨
      (v.2.1 = w.2.1 + 1 ∧ v.1 = w.1))

def adjacent (v w : Triangle) : Prop := upDownAdjacent v w ∨ upDownAdjacent w v

 
def IsPath (N : ℕ) (finish : Triangle) (p : List Triangle) : Prop :=
  p.head? = some (up 0 0) ∧ p.getLast? = some finish ∧ p.Nodup ∧
  p.IsChain adjacent ∧ ∀ v ∈ p, v.2.1 < N

 
def archWeight (N : ℕ) (k : ℤ) (p : List Triangle) : ℝ := by
  classical
  exact if k ≠ 0 ∧ IsPath N (up k 0) p then rho ^ p.length else 0

 
def bridgeWeight (N : ℕ) (k : ℤ) (p : List Triangle) : ℝ := by
  classical
  exact if 0 < N ∧ IsPath N (down k (N - 1)) p then rho ^ p.length else 0

def K (N : ℕ) (k : ℤ) : ℝ := ∑' p, archWeight N k p
def bridgeKernel (N : ℕ) (k : ℤ) : ℝ := ∑' p, bridgeWeight N k p
def archMass (N : ℕ) : ℝ := ∑' k : ℤ, K N k
def bridgeMass (N : ℕ) : ℝ := ∑' k : ℤ, bridgeKernel N k
def moment (N : ℕ) : ℝ := ∑' k : ℕ, (k + 1 : ℝ) * K N (k + 1)

 
def StripSumsFinite (N : ℕ) : Prop :=
  (∀ k : ℤ, Summable (archWeight N k)) ∧
  (∀ k : ℤ, Summable (bridgeWeight N k)) ∧
  Summable (K N) ∧ Summable (bridgeKernel N) ∧
  Summable (fun k : ℕ => (k + 1 : ℝ) * K N (k + 1))

 
def Comparable (f g : ℕ → ℝ) : Prop :=
  ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
    ∀ N : ℕ, 1 ≤ N → lo * g N ≤ f N ∧ f N ≤ hi * g N

 
def CriticalStripMass : Prop :=
  (∀ N : ℕ, 1 ≤ N → StripSumsFinite N) ∧
  (∀ N : ℕ, 1 ≤ N → c * archMass N + bridgeMass N = 1) ∧
  Comparable (fun N => moment (N + 1) - moment N) bridgeMass ∧
  Comparable moment (fun N => (N : ℝ) ^ (3 / 4 : ℝ)) ∧
  Comparable bridgeMass (fun N => (N : ℝ) ^ (-(1 / 4) : ℝ)) ∧
  (∀ N : ℕ, 1 ≤ N → bridgeMass (N + 1) ≤ bridgeMass N)

 

theorem critical_strip_mass : CriticalStripMass := by
  sorry

end
end CriticalStrip

end OAI
