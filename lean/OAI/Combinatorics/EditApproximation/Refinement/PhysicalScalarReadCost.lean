import OAI.Combinatorics.EditApproximation.Refinement.PhysicalScalarFamily
import OAI.Combinatorics.EditApproximation.Probability.FiniteQueryCostOrder

namespace OAI

/-! Each physical group or online source reader requests at most one
scalar. The guards and dependent index transports do not create reads. -/

namespace EditApproximation

section Cost

variable (M J N n exponent F Q R B : ℕ) [NeZero M]
  (oracle : PhysicalScalarKey M J N n exponent F Q R B → ℚ)
  (weight : PhysicalScalarKey M J N n exponent F Q R B → ℕ)
  (bound : ℕ) (hweight : ∀ key, weight key ≤ bound)

omit [NeZero M] in
private theorem groupQuery_transport_cost (b c : ℕ) (h : b = c)
    (queries : PhysicalGroupQueries M J N n exponent F Q R B b)
    (hq : ∀ scale sample, (queries scale sample).cost oracle weight ≤ bound) :
    ∀ scale sample,
      ((Eq.mp (congrArg (PhysicalGroupQueries M J N n exponent F Q R B) h) queries) scale sample).cost
        oracle weight ≤ bound := by
  subst c
  exact hq

omit [NeZero M] in
include hweight in
 theorem physicalScalarGroupRead_cost_le (node : PhysicalInternalNode M J) (time : Fin R)
    (key : GroupScalarKey M F Q) :
    (physicalScalarGroupRead M J N n exponent F Q R B node time key).cost oracle weight ≤ bound := by
  rcases key with ⟨⟨b, cell⟩, scale, sample⟩
  unfold physicalScalarGroupRead physicalScalarGroupQueries
  dsimp only
  split_ifs with hb hc
  · let group : PhysicalLocalGroupKey M J N n exponent :=
      (node, physicalScaleIndex N b hb,
        ⟨cell.1, Nat.lt_succ_of_le hc.1⟩, ⟨cell.2, Nat.lt_succ_of_le hc.2⟩)
    exact groupQuery_transport_cost M J N n exponent F Q R B oracle weight bound
      ((dyadicScales N).get group.2.1) b (physicalScaleIndex_get N b hb)
      (physicalScalarGroupQueriesAt M J N n exponent F Q R B group time)
      (fun _ _ => by simpa only [physicalScalarGroupQueriesAt, FiniteQuery.cost, Nat.add_zero] using hweight _)
      scale sample
  · exact Nat.zero_le _
  · exact Nat.zero_le _

omit [NeZero M] in
include hweight in
 theorem physicalScalarOnlineRead_cost_le (node : PhysicalInternalNode M J) (time : Fin R)
    (key : ℕ × TargetInterval n) (range : ℕ) :
    (physicalScalarOnlineRead M J N n exponent F Q R B node time key range).cost oracle weight ≤ bound := by
  unfold physicalScalarOnlineRead
  split_ifs <;> simp only [FiniteQuery.cost, Nat.add_zero]
  · exact hweight _
  · exact Nat.zero_le _
  · exact Nat.zero_le _

end Cost

section Family

variable {α : Type*} {M J R : ℕ} [NeZero M]
  (target : List α) (N P F exponent H Q passes copies : ℕ)
  (oracle : PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies → ℚ)
  (weight : PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies → ℕ)
  (bound : ℕ) (hweight : ∀ key, weight key ≤ bound)

omit [NeZero M] in
include hweight in
 theorem physicalFamilyGroupRead_cost_le (pass copy : ℕ) (node : PhysicalInternalNode M J)
    (time : Fin R) (key : GroupScalarKey M F Q) :
    (physicalFamilyGroupRead target N P F exponent H Q passes copies pass copy node time key).cost
      oracle weight ≤ bound := by
  rw [physicalFamilyGroupRead, FiniteQuery.mapKeys_cost]
  exact physicalScalarGroupRead_cost_le M J N target.length exponent F Q R (localOnlineMassBound M P H)
    _ _ bound (fun _ => hweight _) node time key

omit [NeZero M] in
include hweight in
 theorem physicalFamilyOnlineRead_cost_le (pass copy : ℕ) (node : PhysicalInternalNode M J)
    (time : Fin R) (key : ℕ × TargetInterval target.length) (range : ℕ) :
    (physicalFamilyOnlineRead target N P F exponent H Q passes copies pass copy node time key range).cost
      oracle weight ≤ bound := by
  rw [physicalFamilyOnlineRead, FiniteQuery.mapKeys_cost]
  exact physicalScalarOnlineRead_cost_le M J N target.length exponent F Q R (localOnlineMassBound M P H)
    _ _ bound (fun _ => hweight _) node time key range

end Family

end EditApproximation

end OAI
