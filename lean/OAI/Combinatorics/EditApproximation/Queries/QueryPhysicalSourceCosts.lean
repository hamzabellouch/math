import OAI.Combinatorics.EditApproximation.Queries.QueryPhysicalScalarCosts

namespace OAI

/-! Complete execution costs of guarded scalar source queries, including
the actual finite address construction and the source lookup. -/

namespace EditApproximation

section Scalar
variable (M J N n exponent F Q R B : ℕ)
  (oracle : PhysicalScalarKey M J N n exponent F Q R B → BinaryFraction)
  (readWork : PhysicalScalarKey M J N n exponent F Q R B → ℕ)
  (W : ℕ) (hW : ∀ key, readWork key ≤ W)

include hW in
theorem queryPhysicalScalarRead_work (key : PhysicalScalarKey M J N n exponent F Q R B) :
    (queryPhysicalScalarRead M J N n exponent F Q R B key).work oracle readWork ≤ 5 * J + 41 + W := by
  have hc := physicalScalarCodeWithWork_cost key
  have hw := hW key
  change _ + 1 + (readWork key + 0) ≤ _
  omega

private theorem queryGroup_cost_transport (b c : ℕ) (h : b = c)
    (actual : BitPhysicalGroupQueries M J N n exponent F Q R B b)
    (K : ℕ) (he : ∀ scale sample, (actual scale sample).work oracle readWork ≤ K) :
    ∀ scale sample,
      ((Eq.mp (congrArg (BitPhysicalGroupQueries M J N n exponent F Q R B) h) actual)
        scale sample).work oracle readWork ≤ K := by
  subst c
  exact he

include hW in
theorem queryPhysicalScalarGroupRead_work (node : PhysicalInternalNode M J) (time : Fin R)
    (key : GroupScalarKey M F Q) :
    (queryPhysicalScalarGroupRead M J N n exponent F Q R B node time key).work oracle readWork ≤
      (queryScalePresentWithWork N key.1.1).2 + (queryCellValidWithWork n exponent key.1.2).2 +
        5 * J + 43 + W := by
  have hc : (queryPhysicalScalarGroupQueries M J N n exponent F Q R B node time
      key.1.1 key.1.2 key.2.1 key.2.2).work oracle readWork ≤ 5 * J + 41 + W := by
    unfold queryPhysicalScalarGroupQueries
    split_ifs with hb hcell
    · exact queryGroup_cost_transport M J N n exponent F Q R B oracle readWork _ _
        (physicalScaleIndex_get N key.1.1 ((queryScalePresentWithWork_value N key.1.1).mp hb))
        _ (5 * J + 41 + W)
        (fun _ _ => queryPhysicalScalarRead_work M J N n exponent F Q R B oracle readWork W hW _)
        key.2.1 key.2.2
    · exact Nat.zero_le _
    · exact Nat.zero_le _
  change _ + _ ≤ _
  omega

include hW in
theorem queryPhysicalScalarOnlineRead_work (node : PhysicalInternalNode M J) (time : Fin R)
    (key : ℕ × TargetInterval n) (range : ℕ) :
    (queryPhysicalScalarOnlineRead M J N n exponent F Q R B node time key range).work oracle readWork ≤
      (queryScalePresentWithWork N key.1).2 + (queryRangeValidWithWork B range).2 + 5 * J + 43 + W := by
  unfold queryPhysicalScalarOnlineRead
  simp only [BitQuery.work]
  split_ifs
  · apply (Nat.add_le_add_left
      (queryPhysicalScalarRead_work M J N n exponent F Q R B oracle readWork W hW _) _).trans
    omega
  · simp only [BitQuery.work]; omega
  · simp only [BitQuery.work]; omega

end Scalar
end EditApproximation

end OAI
