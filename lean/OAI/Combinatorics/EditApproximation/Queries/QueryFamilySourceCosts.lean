import OAI.Combinatorics.EditApproximation.Queries.QueryFamilyScalarReads
import OAI.Combinatorics.EditApproximation.Queries.QueryPhysicalSourceCosts

namespace OAI

namespace EditApproximation

section Family
variable {α : Type*} {M J R : ℕ} (target : List α)
  (N P F exponent H Q passes copies pass copy : ℕ)

theorem queryFamilyTagWithWork_cost (B : ℕ)
    (hp : Nat.size pass ≤ B) (hc : Nat.size copy ≤ B)
    (hps : Nat.size (passes + 1) ≤ B) (hcs : Nat.size (copies + 1) ≤ B)
    (scalar : PhysicalScalarKey M J N target.length exponent F Q R (localOnlineMassBound M P H)) :
    (queryFamilyTagWithWork target N P F exponent H Q passes copies pass copy scalar).2 ≤
      120 * (B + 1) ^ 2 + 5 * J + 55 := by
  have h1 := queryFinOfNatWithWork_cost (passes + 1) pass B (Nat.succ_pos _) hps hp
  have h2 := queryFinOfNatWithWork_cost (copies + 1) copy B (Nat.succ_pos _) hcs hc
  have h3 := physicalFamilyCodeWithWork_cost target N P F exponent H Q passes copies
    ((queryFinOfNatWithWork (passes + 1) pass (Nat.succ_pos _)).1,
      (queryFinOfNatWithWork (copies + 1) copy (Nat.succ_pos _)).1, scalar)
  change (queryFinOfNatWithWork (passes + 1) pass (Nat.succ_pos _)).2 +
    (queryFinOfNatWithWork (copies + 1) copy (Nat.succ_pos _)).2 + _ + 1 ≤ _
  omega

variable
  (oracle : PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies → BinaryFraction)
  (readWork : PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies → ℕ)
  (K W : ℕ)
  (hK : ∀ scalar : PhysicalScalarKey M J N target.length exponent F Q R (localOnlineMassBound M P H),
    (queryFamilyTagWithWork target N P F exponent H Q passes copies pass copy scalar).2 ≤ K)
  (hW : ∀ key, readWork key ≤ W)

include hK hW in
theorem queryFamilyGroupRead_work (node : PhysicalInternalNode M J) (time : Fin R)
    (key : GroupScalarKey M F Q) :
    (queryFamilyGroupRead target N P F exponent H Q passes copies pass copy node time key).work
      oracle readWork ≤ (queryScalePresentWithWork N key.1.1).2 +
        (queryCellValidWithWork target.length exponent key.1.2).2 + 5 * J + 43 + (K + W) := by
  unfold queryFamilyGroupRead
  rw [BitQuery.mapKeysWithWork_work]
  apply queryPhysicalScalarGroupRead_work
  intro scalar
  exact Nat.add_le_add (hK scalar) (hW _)

include hK hW in
theorem queryFamilyOnlineRead_work (node : PhysicalInternalNode M J) (time : Fin R)
    (key : ℕ × TargetInterval target.length) (range : ℕ) :
    (queryFamilyOnlineRead target N P F exponent H Q passes copies pass copy node time key range).work
      oracle readWork ≤ (queryScalePresentWithWork N key.1).2 +
        (queryRangeValidWithWork (localOnlineMassBound M P H) range).2 + 5 * J + 43 + (K + W) := by
  unfold queryFamilyOnlineRead
  rw [BitQuery.mapKeysWithWork_work]
  apply queryPhysicalScalarOnlineRead_work
  intro scalar
  exact Nat.add_le_add (hK scalar) (hW _)

end Family
end EditApproximation

end OAI
