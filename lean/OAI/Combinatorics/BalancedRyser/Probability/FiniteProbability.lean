import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Basic.Real.Basic

namespace OAI

namespace Balanced.FiniteProbability

open scoped BigOperators

def mass {Ω : Type*} (w : Ω → ℝ) (A : Finset Ω) : ℝ :=
  ∑ ω ∈ A, w ω

def avoid {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω]
    (E : ι → Finset Ω) (S : Finset ι) : Finset Ω :=
  Finset.univ.filter (fun ω => ∀ i ∈ S, ω ∉ E i)

end Balanced.FiniteProbability

end OAI
