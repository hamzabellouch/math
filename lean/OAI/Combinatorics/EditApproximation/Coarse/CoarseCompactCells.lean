import OAI.Combinatorics.EditApproximation.Coarse.CoarseArraySimulation

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Leading-zero removal is enough: this property does not assert that a
stored rational is reduced by a gcd. -/
def CoarseCompact (a : BinaryFraction) : Prop :=
  a.width ≤ a.representation.storageBits

 theorem coarseCompact_canonical (a : BinaryFraction) :
    CoarseCompact (canonicalizeWithWork a).1 := by
  change (canonicalizeWithWork a).1.width ≤ _
  rw [canonicalizeWithWork_representation]
  exact canonicalizeWithWork_width_le_storageBits a

 theorem coarseCompact_gridNat (den : List Bool) (hden : 0 < bitWordValue den) (n : ℕ) :
    CoarseCompact (coarseGridNatWithWork den hden n).1 := by
  unfold coarseGridNatWithWork
  exact coarseCompact_canonical _

 theorem coarseCompact_gridAdd (a b : BinaryFraction) :
    CoarseCompact (coarseGridAddWithWork a b).1 := by
  unfold coarseGridAddWithWork
  exact coarseCompact_canonical _

 theorem coarseCompact_min (a b : BinaryFraction) (ha : CoarseCompact a) (hb : CoarseCompact b) :
    CoarseCompact (minWithWork a b).1 := by
  unfold minWithWork
  dsimp only
  split_ifs <;> assumption

 theorem coarseCompact_max (a b : BinaryFraction) (ha : CoarseCompact a) (hb : CoarseCompact b) :
    CoarseCompact (maxWithWork a b).1 := by
  unfold maxWithWork
  dsimp only
  split_ifs <;> assumption

 theorem coarseCompact_divide (a b : BinaryFraction) :
    CoarseCompact (coarseDivideWithWork a b).1 := by
  unfold coarseDivideWithWork fixedDenominatorWithWork
  exact coarseCompact_canonical _

 theorem coarseCompact_contribution (threshold scale a : BinaryFraction)
    (hs : CoarseCompact scale) (ha : CoarseCompact a) :
    CoarseCompact (coarseContributionWithWork threshold scale a).1 := by
  unfold coarseContributionWithWork
  dsimp only
  split_ifs
  · exact coarseCompact_max a scale ha hs
  · exact coarseCompact_gridNat _ _ 0

 theorem coarseCompact_width (a : BinaryFraction) (V D : ℕ)
    (ha : CoarseCompact a) (hv : |a.value| ≤ V)
    (hd : Nat.size a.representation.den ≤ D) :
    a.width ≤ Nat.size V + 2 * D + 1 := by
  apply ha.trans
  exact UnreducedRational.storageBits_le a.representation V D
    (by simpa only [representation_value] using hv) hd

end BinaryFraction
end EditApproximation

end OAI
