import Mathlib

namespace OAI

noncomputable section
namespace AngularEndpoint

def node (N j : ℕ) : ℝ := -1 + 2 * (j : ℝ) / (N : ℝ)

def boundary (N j : ℕ) : ℝ :=
  if j = 0 then -1 else if j = N + 1 then 1 else
    (node N (j - 1) + node N j) / 2

def alpha (N j : ℕ) : ℝ := (1 + (node N j) ^ 2) / 4

def beta (N j : ℕ) : ℝ := node N j / 2

def profile (q : ℝ) : ℝ := (q ^ 2 + q ^ 4) / 16

def radius (τ η : ℝ) (N j : ℕ) : ℝ :=
  1 / 2 + τ ^ 2 * (profile (node N j) + η)

end AngularEndpoint

end

end OAI
