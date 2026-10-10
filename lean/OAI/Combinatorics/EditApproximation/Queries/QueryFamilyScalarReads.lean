import OAI.Combinatorics.EditApproximation.Queries.QueryPhysicalScalarReads
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Counted pass/copy indexing for the independent scalar family.  Both
remainders and the complete family address are computed before lookup. -/

namespace EditApproximation



theorem queryFinOfNatWithWork_value (bound value : ℕ) (hb : 0 < bound) [NeZero bound] :
    (queryFinOfNatWithWork bound value hb).1 = Fin.ofNat bound value := by
  apply Fin.ext
  exact (binaryNaturalDivModWithWork_spec value bound hb).2

theorem queryFinOfNatWithWork_cost (bound value B : ℕ) (hb : 0 < bound)
    (hbound : Nat.size bound ≤ B) (hvalue : Nat.size value ≤ B) :
    (queryFinOfNatWithWork bound value hb).2 ≤ 60 * (B + 1) ^ 2 + 1 := by
  have h := binaryNaturalDivModWithWork_cost value bound
  change (binaryNaturalDivModWithWork value bound).2.2 + 1 ≤ _
  nlinarith only [h, hbound, hvalue, Nat.zero_le B]

section Family
variable {α : Type*} {M J R : ℕ} (target : List α)
  (N P F exponent H Q passes copies pass copy : ℕ)



theorem queryFamilyTagWithWork_value
    (scalar : PhysicalScalarKey M J N target.length exponent F Q R (localOnlineMassBound M P H)) :
    (queryFamilyTagWithWork target N P F exponent H Q passes copies pass copy scalar).1 =
      (Fin.ofNat (passes + 1) pass, Fin.ofNat (copies + 1) copy, scalar) := by
  simp only [queryFamilyTagWithWork, queryFinOfNatWithWork_value]



theorem queryFamilyGroupRead_refines (node : PhysicalInternalNode M J) (time : Fin R)
    (key : GroupScalarKey M F Q) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryFamilyGroupRead target N P F exponent H Q passes copies pass copy node time key)
      (physicalFamilyGroupRead target N P F exponent H Q passes copies pass copy node time key) := by
  exact (queryPhysicalScalarGroupRead_refines M J N target.length exponent F Q R
    (localOnlineMassBound M P H) node time key).mapKeysWithWork _ _
      (queryFamilyTagWithWork_value target N P F exponent H Q passes copies pass copy)



theorem queryFamilyOnlineRead_refines (node : PhysicalInternalNode M J) (time : Fin R)
    (key : ℕ × TargetInterval target.length) (range : ℕ) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryFamilyOnlineRead target N P F exponent H Q passes copies pass copy node time key range)
      (physicalFamilyOnlineRead target N P F exponent H Q passes copies pass copy node time key range) := by
  exact (queryPhysicalScalarOnlineRead_refines M J N target.length exponent F Q R
    (localOnlineMassBound M P H) node time key range).mapKeysWithWork _ _
      (queryFamilyTagWithWork_value target N P F exponent H Q passes copies pass copy)

end Family
end EditApproximation

end OAI
