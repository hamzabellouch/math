import Mathlib

namespace OAI

noncomputable section
namespace CylinderCovering.Cubic

def step (N : ℕ) : ℝ := 2 / N

def node (N i : ℕ) : ℝ := -1 + i * step N

def alpha (a b : ℝ) : ℝ := (1 + a * b) / 2

def beta (a b : ℝ) : ℝ := (a + b) / 2

def profile (q : ℝ) : ℝ := q ^ 2 * (1 + q ^ 2) / 2

def profileMax (a b : ℝ) : ℝ := max (profile a) (profile b)

def cap (ε a b : ℝ) : ℝ := 1 + ε ^ 2 * profileMax a b + 100 * ε ^ 3

def Sector (a b r z : ℝ) : Prop := 0 ≤ r ∧ a * r ≤ z ∧ z ≤ b * r

def LowerHit (N j : ℕ) (ε x y z : ℝ) : Prop :=
  Sector (node N j) (node N (j + 1))
    (1 + z - ε * x * beta (node N j) (node N (j + 1)))
    (y - ε * x * alpha (node N j) (node N (j + 1))) ∧
  1 + z - ε * x * beta (node N j) (node N (j + 1)) ≤
    cap ε (node N j) (node N (j + 1))

def UpperHit (N j : ℕ) (ε x y z : ℝ) : Prop :=
  Sector (node N j) (node N (j + 1))
    (1 - z + ε * y * beta (node N j) (node N (j + 1)))
    (x + ε * y * alpha (node N j) (node N (j + 1))) ∧
  1 - z + ε * y * beta (node N j) (node N (j + 1)) ≤
    cap ε (node N j) (node N (j + 1))

end CylinderCovering.Cubic

end

end OAI
