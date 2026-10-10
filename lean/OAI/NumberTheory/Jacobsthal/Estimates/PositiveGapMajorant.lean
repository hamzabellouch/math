import Mathlib.Topology.UrysohnsLemma
import OAI.NumberTheory.Jacobsthal.Primes.PrimeOccupationDensity

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PositiveGapMajorant

open _root_.Set

theorem exists_positive_gap_majorant (K : ℝ) : ∃ H : C(ℝ×ℝ,ℝ),
    HasCompactSupport H ∧ (∀ x,0 ≤ H x ∧ H x ≤ 1) ∧
    (∀ r s,2 ≤ r → r ≤ K → 0 ≤ s → s ≤ K → H (r,s)=1) ∧
    ∀ r s,r < 1 ∨ K+1 < r → H (r,s)=0 := by
  let A : Set (ℝ×ℝ) := Icc (2,0) (K,K)
  let Z : Set (ℝ×ℝ) := {x | x.1 ≤ 1} ∪ {x | K+1 ≤ x.1}
  have hA : IsCompact A := isCompact_Icc
  have hZ : IsClosed Z := (isClosed_le continuous_fst continuous_const).union
    (isClosed_le continuous_const continuous_fst)
  have hd : Disjoint A Z := by
    apply Set.disjoint_left.mpr
    intro x hx hz
    have hlow : 2 ≤ x.1 := hx.1.1
    have hhigh : x.1 ≤ K := hx.2.1
    rcases hz with hz | hz
    · change x.1 ≤ 1 at hz
      linarith
    · change K+1 ≤ x.1 at hz
      linarith
  obtain ⟨H,hHA,hHZ,hcompact,hbounds⟩ := exists_continuous_one_zero_of_isCompact hA hZ hd
  refine ⟨H,hcompact,hbounds,?_,?_⟩
  · intro r s hr hrK hs hsK
    exact hHA ⟨⟨hr,hs⟩,⟨hrK,hsK⟩⟩
  · intro r s hbad
    apply hHZ
    rcases hbad with h | h
    · exact Or.inl h.le
    · exact Or.inr h.le

end NumberTheoryLean.PositiveGapMajorant

end

end Erdos970

end OAI
