import OAI.Combinatorics.EditApproximation.Queries.QueryFamilyScalarReads

namespace OAI

namespace EditApproximation.BitQuery

theorem mapKeysWithWork_value {ι κ β : Type*} (f : ι → κ × ℕ)
    (program : BitQuery ι β) (oracle : κ → BinaryFraction) :
    (mapKeysWithWork f program).value oracle = program.value (fun key => oracle (f key).1) := by
  induction program with
  | done result => rfl
  | charge steps next ih => exact ih
  | read key next ih => exact ih (oracle (f key).1)

end EditApproximation.BitQuery

namespace EditApproximation
section Scalar
variable (M J N n exponent F Q R B : ℕ)
  (oracle : PhysicalScalarKey M J N n exponent F Q R B → BinaryFraction)
  (V : ℕ) (hV : 2 ≤ V) (hv : ∀ key, (oracle key).width ≤ V)

private theorem group_width_transport (b c : ℕ) (h : b = c)
    (actual : BitPhysicalGroupQueries M J N n exponent F Q R B b)
    (hwidth : ∀ scale sample, ((actual scale sample).value oracle).width ≤ V) :
    ∀ scale sample,
      (((Eq.mp (congrArg (BitPhysicalGroupQueries M J N n exponent F Q R B) h) actual)
        scale sample).value oracle).width ≤ V := by
  subst c
  exact hwidth

include hV hv in
theorem queryPhysicalScalarGroupRead_width (node : PhysicalInternalNode M J) (time : Fin R)
    (key : GroupScalarKey M F Q) :
    ((queryPhysicalScalarGroupRead M J N n exponent F Q R B node time key).value oracle).width ≤ V := by
  simp only [queryPhysicalScalarGroupRead, BitQuery.value]
  unfold queryPhysicalScalarGroupQueries
  split_ifs with hb hcell
  · refine group_width_transport M J N n exponent F Q R B oracle V _ _
      (physicalScaleIndex_get N key.1.1 ((queryScalePresentWithWork_value N key.1.1).mp hb))
      _ ?_ key.2.1 key.2.2
    intro scale sample
    exact hv _
  · exact (BinaryFraction.nat_width_le 0).trans (by simpa only [Nat.size_zero, Nat.zero_add] using hV)
  · exact (BinaryFraction.nat_width_le 0).trans (by simpa only [Nat.size_zero, Nat.zero_add] using hV)

include hV hv in
theorem queryPhysicalScalarOnlineRead_width (node : PhysicalInternalNode M J) (time : Fin R)
    (key : ℕ × TargetInterval n) (range : ℕ) :
    ((queryPhysicalScalarOnlineRead M J N n exponent F Q R B node time key range).value oracle).width ≤ V := by
  unfold queryPhysicalScalarOnlineRead
  simp only [BitQuery.value]
  split_ifs
  · exact hv _
  · exact (BinaryFraction.nat_width_le 0).trans (by simpa only [Nat.size_zero, Nat.zero_add] using hV)
  · exact (BinaryFraction.nat_width_le 0).trans (by simpa only [Nat.size_zero, Nat.zero_add] using hV)

end Scalar

section Family
variable {α : Type*} {M J R : ℕ} (target : List α)
  (N P F exponent H Q passes copies pass copy V : ℕ)
  (oracle : PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies → BinaryFraction)
  (hV : 2 ≤ V) (hv : ∀ key, (oracle key).width ≤ V)

include hV hv in
theorem queryFamilyGroupRead_width (node : PhysicalInternalNode M J) (time : Fin R)
    (key : GroupScalarKey M F Q) :
    ((queryFamilyGroupRead target N P F exponent H Q passes copies pass copy node time key).value oracle).width ≤ V := by
  rw [queryFamilyGroupRead, BitQuery.mapKeysWithWork_value]
  exact queryPhysicalScalarGroupRead_width M J N target.length exponent F Q R _ _ V hV (fun _ => hv _) node time key

include hV hv in
theorem queryFamilyOnlineRead_width (node : PhysicalInternalNode M J) (time : Fin R)
    (key : ℕ × TargetInterval target.length) (range : ℕ) :
    ((queryFamilyOnlineRead target N P F exponent H Q passes copies pass copy node time key range).value oracle).width ≤ V := by
  rw [queryFamilyOnlineRead, BitQuery.mapKeysWithWork_value]
  exact queryPhysicalScalarOnlineRead_width M J N target.length exponent F Q R _ _ V hV (fun _ => hv _) node time key range

end Family
end EditApproximation

end OAI
