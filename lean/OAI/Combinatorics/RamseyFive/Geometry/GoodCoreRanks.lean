import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.Cores
import OAI.Combinatorics.RamseyFive.Entropy.GoodEndpoints

namespace OAI

namespace SharpRamseyFive.CoreGeometry
open Module SharpRamseyFive.FiniteEntropy
open scoped LinearAlgebra.Projectivization BigOperators Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

theorem goodFirst_core_rank (hdim : finrank K V=5)
    (p : Law (ℙ K V × ℙ K (Module.Dual K V))) (A s : ℝ)
    (hA : 0 < A) (hs : 2 ≤ s) (a : ℙ K V)
    (ha : a∈goodFirstEndpoints p A ((Nat.card K:ℝ)^4) s) :
    ⌈5-(Real.log A+3*s)/Real.log (Nat.card K)⌉₊ ≤
      finrank K (firstCore p Projectivization.rep a) := by
  have hq : 0 < (Nat.card K : ℝ) := by
    exact_mod_cast (Finite.card_pos : 0 < Nat.card K)
  apply core_dimension_lower (by rw [Subspace.dual_finrank_eq,hdim])
    (fiber p a) A s hA hs (heavyRow p ((Nat.card K:ℝ)^4) s a)
  · intro b hb
    exact goodFirst_conditional_cap p A _ s hA (pow_pos hq 4) a ha b hb
  · exact (Finset.mem_filter.mp ha).2.2

theorem goodSecond_core_rank (hdim : finrank K V=5)
    (p : Law (ℙ K V × ℙ K (Module.Dual K V))) (B s : ℝ)
    (hB : 0 < B) (hs : 2 ≤ s) (b : ℙ K (Module.Dual K V))
    (hb : b∈goodFirstEndpoints (swap p) B ((Nat.card K:ℝ)^4) s) :
    ⌈5-(Real.log B+3*s)/Real.log (Nat.card K)⌉₊ ≤
      finrank K (secondCore (K := K) p Projectivization.rep b) := by
  have hq : 0 < (Nat.card K : ℝ) := by
    exact_mod_cast (Finite.card_pos : 0 < Nat.card K)
  apply core_dimension_lower hdim (fiber (swap p) b) B s hB hs
    (heavyRow (swap p) ((Nat.card K:ℝ)^4) s b)
  · intro a ha
    exact goodFirst_conditional_cap (swap p) B _ s hB (pow_pos hq 4) b hb a ha
  · exact (Finset.mem_filter.mp hb).2.2
end
end SharpRamseyFive.CoreGeometry

end OAI
