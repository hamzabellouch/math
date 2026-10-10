import OAI.NumberTheory.Ostmann.FiniteSummands
import OAI.NumberTheory.Ostmann.Preliminaries.Residues

namespace OAI

/-!
# Reduction of Ostmann's conjecture to two infinite summands

The equivalence here is a reduction, not a proof of either main statement.
In particular, the two-infinite-summand assertion is not a published input.
The finite-factor argument has been proved using library Dirichlet and CRT.
-/

namespace Ostmann

open scoped symmDiff

/-- Reduction described after Theorem 2.3 in the manuscript. -/
theorem inverseGoldbach_of_twoInfiniteSummandsImpossible
    (hmain : TwoInfiniteSummandsImpossible) : InverseGoldbach := by
  intro A B hA hB hfinite
  have heventual := (finite_symmDiff_iff A B).mp hfinite
  obtain ⟨hAi, hBi⟩ := infinite_summands hA hB heventual
  exact hmain A B hAi hBi heventual

/-- The technical two-infinite-set assertion follows from the main statement. -/
theorem twoInfiniteSummandsImpossible_of_inverseGoldbach
    (hmain : InverseGoldbach) : TwoInfiniteSummandsImpossible := by
  intro A B hA hB heventual
  exact hmain A B hA.nontrivial hB.nontrivial ((finite_symmDiff_iff A B).mpr heventual)

/-- Finite summands create no additional unresolved case of the conjecture. -/
theorem inverseGoldbach_iff_twoInfiniteSummandsImpossible :
    InverseGoldbach ↔ TwoInfiniteSummandsImpossible :=
  ⟨twoInfiniteSummandsImpossible_of_inverseGoldbach,
    inverseGoldbach_of_twoInfiniteSummandsImpossible⟩

/-- The finite-modification wording follows from the symmetric-difference wording. -/
theorem no_decomposition_of_finite_modification
    (hmain : InverseGoldbach) {P A B : Set ℕ}
    (hP : (P ∆ primes).Finite) (hA : A.Nontrivial) (hB : B.Nontrivial) :
    sumset A B ≠ P := by
  intro heq
  exact hmain A B hA hB (heq ▸ hP)

end Ostmann

end OAI
