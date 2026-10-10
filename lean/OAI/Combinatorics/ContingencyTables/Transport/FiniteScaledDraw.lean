import OAI.Combinatorics.ContingencyTables.Machines.FiniteFairBits
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordWalk
import OAI.Combinatorics.ContingencyTables.Transport.BoundedOffsetLaw

namespace OAI

/-! # The bounded quotient draw is realized by an actual Boolean word -/

namespace ContingencyTables.FairBits

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section

def scaledInteger (M k : ℕ) (hM : 0 < M) (z : Fin (2 ^ k)) : Fin M :=
  ⟨M * z.val / 2 ^ k, by
    rw [← scale_eq_div]
    exact scale_lt hM (pow_pos (by decide) k) z.isLt⟩

theorem scaledIntegerLaw_eq (M k : ℕ) (hM : 0 < M) :
    mapLaw (uniformLaw (α := Fin (2 ^ k))) (scaledInteger M k hM) = scaledLaw M k hM := by
  apply RationalLaw.ext
  funext β
  rw [uniform_map_mass]
  change (∑ z : Fin (2 ^ k), if scaledInteger M k hM z = β then (1 : ℚ) else 0) /
    Fintype.card (Fin (2 ^ k)) = outputMass M (2 ^ k) β.val
  simp only [scaledInteger, Fin.ext_iff, ← scale_eq_div, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun z : ℕ =>
    if scale M (2 ^ k) z = β.val then (1 : ℚ) else 0) (2 ^ k)]
  unfold outputMass fiber
  rw [← Finset.sum_filter]
  simp

def scaledBitInteger (M k : ℕ) (hM : 0 < M) (bits : Fin k → Bool) : Fin M :=
  scaledInteger M k hM (binaryWordEquiv k bits)

/-- The exact law of the finite Boolean quotient operation is the law
used in the dense offset error estimate and the tabulation formula. -/
theorem scaledBitIntegerLaw_eq (M k : ℕ) (hM : 0 < M) :
    mapLaw (uniformLaw (α := Fin k → Bool)) (scaledBitInteger M k hM) = scaledLaw M k hM := by
  unfold scaledBitInteger
  rw [← map_equiv (binaryWordEquiv k), uniform_equiv]
  exact scaledIntegerLaw_eq M k hM

end

end ContingencyTables.FairBits

end OAI
