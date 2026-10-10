import OAI.Combinatorics.EditApproximation.Queries.QueryPhysicalScalarGuards
import OAI.Combinatorics.EditApproximation.Binary.BitQueryKeys
import OAI.Combinatorics.EditApproximation.Geometry.MemoCodeWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Concrete scalar-source adapters.  Guards, finite source addresses and
tag construction are executed before each read; rejected requests return
the original zero value without exposing a random coordinate. -/

namespace EditApproximation

section Scalar
variable (M J N n exponent F Q R B : ℕ)





theorem queryPhysicalScalarRead_refines (key : PhysicalScalarKey M J N n exponent F Q R B) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryPhysicalScalarRead M J N n exponent F Q R B key) (.read key .done) :=
  .charge _ (.read key _ _ (fun _ => .done rfl))







private theorem queryGroup_transport (b c : ℕ) (h : b = c)
    (actual : BitPhysicalGroupQueries M J N n exponent F Q R B b)
    (expected : PhysicalGroupQueries M J N n exponent F Q R B b)
    (he : ∀ scale sample, BitQuery.Refines (fun word value => word.value = value)
      (actual scale sample) (expected scale sample)) :
    ∀ scale sample, BitQuery.Refines (fun word value => word.value = value)
      ((Eq.mp (congrArg (BitPhysicalGroupQueries M J N n exponent F Q R B) h) actual) scale sample)
      ((Eq.mp (congrArg (PhysicalGroupQueries M J N n exponent F Q R B) h) expected) scale sample) := by
  subst c
  exact he

theorem queryPhysicalScalarGroupRead_refines (node : PhysicalInternalNode M J) (time : Fin R)
    (key : GroupScalarKey M F Q) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryPhysicalScalarGroupRead M J N n exponent F Q R B node time key)
      (physicalScalarGroupRead M J N n exponent F Q R B node time key) := by
  apply BitQuery.Refines.charge
  rcases key with ⟨⟨b, cell⟩, scale, sample⟩
  unfold queryPhysicalScalarGroupQueries physicalScalarGroupRead physicalScalarGroupQueries
  dsimp only
  by_cases hb : b ∈ dyadicScales N
  · rw [dite_eq_left hb, dite_eq_left ((queryScalePresentWithWork_value N b).mpr hb)]
    by_cases hc : cell.1 ≤ n * 2 ^ exponent ∧ cell.2 ≤ n * 2 ^ exponent
    · rw [dite_eq_left hc, dite_eq_left ((queryCellValidWithWork_value n exponent cell).mpr hc)]
      exact queryGroup_transport M J N n exponent F Q R B _ b (physicalScaleIndex_get N b hb)
        _ _ (fun _ _ => queryPhysicalScalarRead_refines M J N n exponent F Q R B _) scale sample
    · rw [dite_eq_right hc, dite_eq_right
        (fun h => hc ((queryCellValidWithWork_value n exponent cell).mp h))]
      exact .done (by simp only [BinaryFraction.nat_value, Nat.cast_zero])
  · rw [dite_eq_right hb, dite_eq_right
      (fun h => hb ((queryScalePresentWithWork_value N b).mp h))]
    exact .done (by simp only [BinaryFraction.nat_value, Nat.cast_zero])



theorem queryPhysicalScalarOnlineRead_refines (node : PhysicalInternalNode M J) (time : Fin R)
    (key : ℕ × TargetInterval n) (range : ℕ) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryPhysicalScalarOnlineRead M J N n exponent F Q R B node time key range)
      (physicalScalarOnlineRead M J N n exponent F Q R B node time key range) := by
  apply BitQuery.Refines.charge
  unfold physicalScalarOnlineRead
  by_cases hb : key.1 ∈ dyadicScales N
  · rw [dite_eq_left hb, dite_eq_left ((queryScalePresentWithWork_value N key.1).mpr hb)]
    by_cases hr : 0 < range ∧ range ≤ B
    · rw [dite_eq_left hr, dite_eq_left ((queryRangeValidWithWork_value B range).mpr hr)]
      exact queryPhysicalScalarRead_refines M J N n exponent F Q R B _
    · rw [dite_eq_right hr, dite_eq_right (fun h => hr ((queryRangeValidWithWork_value B range).mp h))]
      exact .done (by simp only [BinaryFraction.nat_value, Nat.cast_zero])
  · rw [dite_eq_right hb, dite_eq_right (fun h => hb ((queryScalePresentWithWork_value N key.1).mp h))]
    exact .done (by simp only [BinaryFraction.nat_value, Nat.cast_zero])

end Scalar
end EditApproximation

end OAI
