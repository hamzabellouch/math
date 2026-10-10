import OAI.Combinatorics.EditApproximation.Binary.BinaryRepresentativeKernel
import OAI.Combinatorics.EditApproximation.Binary.BinaryMedianKernel
import OAI.Combinatorics.EditApproximation.Geometry.LocalInitialCones
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Literal initial-cone arithmetic on gathered integer seed entries. The
local grid list is supplied by its bounded enumerator; all values, ceilings,
spatial charges and the fallback minimum are computed on binary storage. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem ofNaturalWord_value (bits : List Bool) :
    (ofNaturalWord bits).value = (bitWordValue bits : ℚ) := by
  simp only [ofNaturalWord, value, SignedBinary.value, signedMagnitude, Bool.false_eq_true,
    ↓reduceIte, Int.cast_natCast, bitWordValue, Bool.toNat_true, Nat.mul_zero, Nat.add_zero,
    Nat.cast_one, div_one]

@[simp] theorem ofNaturalWord_width (bits : List Bool) :
    (ofNaturalWord bits).width = max bits.length 1 := rfl



@[simp] theorem scaledSeedWithWork_value (U : ℕ) (a gap : BinaryFraction) :
    (scaledSeedWithWork U a gap).1.value = scaledSeedValue U a.value gap.value := by
  simp only [scaledSeedWithWork, maxWithWork_value, ofNaturalWord_value,
    naturalCeilingWithWork_value, divWithWork_value, nat_value, absolute_value, scaledSeedValue]



@[simp] theorem initialConeWithWork_value {α : Type*} (source target : List α)
    (U : TargetInterval target.length → ℕ) (a L : BinaryFraction)
    (query center : TargetInterval target.length) :
    (initialConeWithWork source.length U a L query center).1.value =
      initialConeValue source target U a.value L.value query center := by
  simp only [initialConeWithWork, canonicalAddWithWork_value, canonicalMulWithWork_value,
    scaledSeedWithWork_value, stateGapWithWork_value, endpointDistanceWithWork_value,
    initialConeValue, rationalStateGap]

/-- The local initial-cone arithmetic after the center list has been
constructed and the corresponding seed values gathered. -/
def initialMinimumWithWork {n : ℕ} (sourceLength : ℕ) (U : TargetInterval n → ℕ)
    (N F : ℕ) (a : BinaryFraction) (query : TargetInterval n) (centers : List (TargetInterval n)) :
    BinaryFraction × ℕ :=
  let zeroTest := naturalEqualWithWork (U query) 0
  if zeroTest.1 then (zero, zeroTest.2 + 1) else
    let L := canonicalMulWithWork (nat 32) (nat F)
    let coefficient := canonicalAddWithWork L.1 one
    let fallback := canonicalMulWithWork coefficient.1 (nat N)
    let scores := arithmeticMapWithWork (initialConeWithWork sourceLength U a L.1 query) centers
    let result := minimumWithWork fallback.1 scores.1
    (result.1, zeroTest.2 + L.2 + coefficient.2 + fallback.2 + scores.2 + result.2 +
      Nat.size F + Nat.size N + 6)

theorem initialMinimumWithWork_value {α : Type*} (source target : List α)
    (U : TargetInterval target.length → ℕ) (N P F : ℕ) (A : ℚ) (a : BinaryFraction)
    (query : TargetInterval target.length) :
    (initialMinimumWithWork source.length U N F a query
      (localInitialConeCenters N P A U query)).1.value =
      localInitialConeTable source target U N P F A a.value query := by
  have hzero : (naturalEqualWithWork (U query) 0).1 = true ↔ U query = 0 :=
    naturalEqualWithWork_value _ _
  unfold initialMinimumWithWork localInitialConeTable
  by_cases hz : U query = 0
  · rw [ite_eq_left (hzero.mpr hz), ite_eq_left hz]
    rw [← representation_value, zero_representation, UnreducedRational.value_zero]
  · rw [ite_eq_right (fun h => hz (hzero.mp h)), ite_eq_right hz]
    simp only [minimumWithWork_value, canonicalMulWithWork_value, canonicalAddWithWork_value,
      arithmeticMapWithWork_value, List.map_map, Function.comp_def, initialConeWithWork_value,
      nat_value, one, Nat.cast_one, Nat.cast_ofNat]

end BinaryFraction
end EditApproximation

end OAI
