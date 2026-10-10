import OAI.LinearAlgebra.CirculantHadamard.Model
import Lean.Elab.Tactic.Omega

namespace OAI

namespace CirculantHadamard.Barker

open scoped BigOperators

def aperiodic {n : ℕ} (h : Fin n → ℤ) (k : ℕ) : ℤ :=
  ∑ j : Fin (n - k), h ⟨j.val, by omega⟩ * h ⟨j.val + k, by omega⟩

def periodic {n : ℕ} [NeZero n] (h : Fin n → ℤ) (a : Fin n) : ℤ :=
  ∑ j : Fin n, h j * h (j - a)

def IsBarker {n : ℕ} (h : Fin n → ℤ) : Prop :=
  (∀ j, IsSign (h j)) ∧ ∀ k : ℕ, 0 < k → k < n → |aperiodic h k| ≤ 1

end CirculantHadamard.Barker

end OAI
