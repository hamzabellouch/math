import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.GoodCoreRanks

namespace OAI

namespace SharpRamseyFive.CoreGeometry
open Module SharpRamseyFive.FiniteEntropy
open scoped LinearAlgebra.Projectivization BigOperators Classical
noncomputable section

lemma rank_of_logarithmic_slack {q A s : ℝ} {r n : ℕ}
    (hq : 1<q) (hslack : Real.log A+3*s < (6-(r:ℝ))*Real.log q)
    (hcore : ⌈5-(Real.log A+3*s)/Real.log q⌉₊ ≤ n) : r≤n := by
  have hl : 0<Real.log q := Real.log_pos hq
  have hd : (r:ℝ)-1 < 5-(Real.log A+3*s)/Real.log q := by
    have := (div_lt_iff₀ hl).mpr hslack
    linarith
  have hn : 5-(Real.log A+3*s)/Real.log q ≤ (n:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hcore)
  by_contra h
  have hnr : n+1≤r := by omega
  have hnr' : (n:ℝ)+1≤(r:ℝ) := by exact_mod_cast hnr
  linarith

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

theorem goodFirst_integer_rank (hdim : finrank K V=5)
    (p : Law (ℙ K V × ℙ K (Module.Dual K V))) (A s : ℝ)
    (hA : 0<A) (hs : 2 ≤ s) (r : ℕ)
    (hcap : Real.log A+3*s < (6-(r:ℝ))*Real.log (Nat.card K))
    (a : ℙ K V) (ha : a∈goodFirstEndpoints p A ((Nat.card K:ℝ)^4) s) :
    r ≤ finrank K (firstCore p Projectivization.rep a) := by
  apply rank_of_logarithmic_slack (by exact_mod_cast (Finite.one_lt_card (α := K))) hcap
  exact goodFirst_core_rank hdim p A s hA hs a ha

theorem goodSecond_integer_rank (hdim : finrank K V=5)
    (p : Law (ℙ K V × ℙ K (Module.Dual K V))) (B s : ℝ)
    (hB : 0<B) (hs : 2 ≤ s) (r : ℕ)
    (hcap : Real.log B+3*s < (6-(r:ℝ))*Real.log (Nat.card K))
    (b : ℙ K (Module.Dual K V))
    (hb : b∈goodFirstEndpoints (swap p) B ((Nat.card K:ℝ)^4) s) :
    r ≤ finrank K (secondCore (K := K) p Projectivization.rep b) := by
  apply rank_of_logarithmic_slack (by exact_mod_cast (Finite.one_lt_card (α := K))) hcap
  exact goodSecond_core_rank hdim p B s hB hs b hb
end
end SharpRamseyFive.CoreGeometry

end OAI
