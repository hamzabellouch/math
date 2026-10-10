import Mathlib

namespace OAI

namespace ShortEgyptian

def IsExpansion (a b : ℕ) (ns : List ℕ) : Prop :=
  ns.Pairwise (· < ·) ∧ (∀ n ∈ ns, 2 ≤ n) ∧
    (ns.map (fun n => (1 : ℚ) / (n : ℚ))).sum = (a : ℚ) / (b : ℚ)

noncomputable def minLength (a b : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ ns : List ℕ, IsExpansion a b ns ∧ ns.length = k}

noncomputable def maxMinLength (b : ℕ) : ℕ :=
  (Finset.Ico 1 b).sup (fun a => minLength a b)

end ShortEgyptian

end OAI
