import Mathlib

namespace OAI

noncomputable section
namespace CylinderCovering.RadialRiemann
open Set

def step (a b : ℝ) (N : ℕ) : ℝ := (b - a) / N

def point (a b : ℝ) (N i : ℕ) : ℝ := a + i * step a b N

def cell (a b : ℝ) (N : ℕ) (i : Fin N) : Set ℝ :=
  Icc (point a b N i) (point a b N (i + 1))

def IsTagged (a b : ℝ) (N : ℕ) (tag : Fin N → ℝ) : Prop :=
  ∀ i, tag i ∈ cell a b N i

def capMax (R : ℝ → ℝ) (a b : ℝ) (N : ℕ) (i : Fin N) : ℝ :=
  sSup (R '' cell a b N i)

def mixedSum (F : ℝ → ℝ → ℝ) (a b : ℝ) (N : ℕ)
    (leftTag rightTag : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, step a b N * F (leftTag i) (rightTag i)

def collarSum (R W : ℝ → ℝ) (K a b : ℝ) (N : ℕ) (tag : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, step a b N * (capMax R a b N i + K * step a b N)^2 * W (tag i)

end CylinderCovering.RadialRiemann

end

end OAI
