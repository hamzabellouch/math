import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

namespace Invariant233.MixedRadix

def denominator (r : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, r i

abbrev Digits (r : ℕ → ℕ) := (n : ℕ) → Fin (r n)

noncomputable def term {r : ℕ → ℕ} (d : Digits r) (n : ℕ) : ℝ :=
  (d n : ℝ) / (denominator r (n + 1) : ℝ)

noncomputable def ofDigits {r : ℕ → ℕ} (d : Digits r) : ℝ :=
  ∑' n, term d n

noncomputable def tailValue {r : ℕ → ℕ} (d : Digits r) (j : ℕ) : ℝ :=
  (denominator r j : ℝ) * ∑' n, term d (j + n)

def prefixRank {r : ℕ → ℕ} (d : Digits r) : ℕ → ℕ
  | 0 => 0
  | n + 1 => prefixRank d n * r n + (d n : ℕ)

def Nonterminal {r : ℕ → ℕ} (d : Digits r) : Prop :=
  ∀ j, ∃ n, j ≤ n ∧ (d n : ℕ) + 1 < r n

noncomputable def canonicalDigits (r : ℕ → ℕ) (hr : ∀ n, 0 < r n) (x : ℝ) : Digits r :=
  fun n => ⟨⌊(denominator r (n + 1) : ℝ) * x⌋₊ % r n, Nat.mod_lt _ (hr n)⟩

def extendPrefix (r : ℕ → ℕ) (hr : ∀ n, 0 < r n) (N : ℕ)
    (d : (i : Fin N) → Fin (r i)) : Digits r :=
  fun n => if h : n < N then d ⟨n, h⟩ else ⟨0, hr n⟩

def radices (q : ℕ → ℕ) (n : ℕ) : ℕ := q (n + 1) / q n

def hybrid {r : ℕ → ℕ} (d e : Digits r) (N : ℕ) : Digits r :=
  fun n => if n < N then e n else d n

end Invariant233.MixedRadix

end OAI
