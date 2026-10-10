import OAI.Combinatorics.EditApproximation.Binary.BinarySampledGroups
import OAI.Combinatorics.EditApproximation.Binary.BinaryRoundedWork

namespace OAI

/-! Full bit cost of the sampled member continuation. All its internal
counting, envelope, rounding and summation callbacks are discharged here. -/

namespace EditApproximation
namespace BinaryFraction

def sampledMemberInputBudget (M b B : ℕ) : ℕ :=
  B + (3 * bandEnvelopeWordBudget b M B + 1) + connectionWordBudget M B + 1

def sampledMemberWordBudget (M T b B : ℕ) : ℕ :=
  let S := sampledMemberInputBudget M b B
  groupMemberWordBudget T S (boundedScaleWordBudget M S)

def sampledMemberBitBudget (M T exponent b vertices B : ℕ) : ℕ :=
  M * (bandEnvelopeBitBudget b M vertices B + 6) +
    roundedBandBitBudget exponent b M vertices B + 7 * M +
    (connectionBitBudget M B + 2 * B + M + 2) +
    countedGroupBitBudget M T (sampledMemberInputBudget M b B) + 5

theorem unskippedEstimateWithWork_bounds {α : Type*} (source target : List α) {M T : ℕ}
    (parent : TargetInterval source.length) (b P exponent Q : ℕ) (tau F : BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (scales : Fin T → BinaryFraction)
    (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)
    (member : UnskippedBand source target parent b P exponent tau.value F.value
      (fun i q => (child i q).value) (fun i q => (initial i q).value))
    (B : ℕ) (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B)
    (hb : Nat.size b + 2 ≤ B) (hny : Nat.size target.length + 2 ≤ B)
    (hs : ∀ t, (scales t).width ≤ B)
    (hi : ∀ action ∈ member.actions, ∀ i, (initial i (action i)).width ≤ B)
    (hv : ∀ i q, (current i q).width ≤ B) :
    (unskippedEstimateWithWork source target parent b P exponent Q tau F child initial current
      scales draw member).1.width ≤ sampledMemberWordBudget M T b B ∧
    (unskippedEstimateWithWork source target parent b P exponent Q tau F child initial current
      scales draw member).2 ≤ sampledMemberBitBudget M T exponent b member.actions.length B := by
  let mass := envelopeVectorWithWork b member.actions initial
  let rounded := roundedBandWithWork exponent b member.actions member.nonempty initial
  let values := vectorMapWithWork M fun i => (current i (rounded.1.get i), 1)
  let connection := endpointConnectionWithWork member.center rounded.1.get
  let S := sampledMemberInputBudget M b B
  have hBS : B ≤ S := by dsimp only [S, sampledMemberInputBudget]; omega
  have hmass (i : Fin M) : (mass.1.get i).width ≤ 3 * bandEnvelopeWordBudget b M B + 1 := by
    simp only [mass, envelopeVectorWithWork, vectorMapWithWork_value]
    exact bandEnvelopeWithWork_width b member.actions initial i B (fun a ha => hi a ha i)
  have hmassc := vectorMapWithWork_cost_le M (bandEnvelopeWithWork b member.actions initial)
    (bandEnvelopeBitBudget b M member.actions.length B) (fun i =>
      bandEnvelopeWithWork_cost b member.actions initial i B (fun a ha => hi a ha i))
  change mass.2 ≤ _ at hmassc
  have hroundc := roundedBandWithWork_cost exponent b member.actions member.nonempty initial B
    (by omega) hi
  change rounded.2 ≤ _ at hroundc
  have hvalue (i : Fin M) : (values.1.get i).width ≤ B := by
    simp only [values, vectorMapWithWork_value]
    exact hv i _
  have hvaluec := vectorMapWithWork_cost_le M (fun i => (current i (rounded.1.get i), 1)) 1
    (fun _ => le_rfl)
  change values.2 ≤ _ at hvaluec
  have hcenterlo : Nat.size member.center.lo + 2 ≤ B :=
    (Nat.add_le_add_right (Nat.size_le_size (member.center.ordered.trans member.center.valid)) 2).trans hny
  have hcenterhi : Nat.size member.center.hi + 2 ≤ B :=
    (Nat.add_le_add_right (Nat.size_le_size member.center.valid) 2).trans hny
  have hstates : ∀ s ∈ List.ofFn rounded.1.get,
      Nat.size s.lo + 2 ≤ B ∧ Nat.size s.hi + 2 ≤ B := by
    intro s _
    exact ⟨(Nat.add_le_add_right (Nat.size_le_size (s.ordered.trans s.valid)) 2).trans hny,
      (Nat.add_le_add_right (Nat.size_le_size s.valid) 2).trans hny⟩
  have hcw := connectionWithWork_width (nat member.center.lo) (nat member.center.hi)
    (List.ofFn rounded.1.get) B ((nat_width_le _).trans hcenterlo)
    ((nat_width_le _).trans hcenterhi) hstates
  have hcc := connectionWithWork_cost (nat member.center.lo) (nat member.center.hi)
    (List.ofFn rounded.1.get) B ((nat_width_le _).trans hcenterlo)
    ((nat_width_le _).trans hcenterhi) hstates
  simp only [List.length_ofFn] at hcw hcc
  have hconnw : connection.1.width ≤ connectionWordBudget M B := hcw
  have hconnc : connection.2 ≤ connectionBitBudget M B + 2 * B + M + 2 := by
    change _ + Nat.size member.center.lo + Nat.size member.center.hi + M + 2 ≤ _
    omega
  have hmember := countedGroupMemberWithWork_bounds Q b scales connection.1 mass.1 values.1 draw S
    (by omega) (hM.trans hBS) (hQ.trans hBS) (hb.trans hBS) (fun t => (hs t).trans hBS)
    (hconnw.trans (by dsimp only [S, sampledMemberInputBudget]; omega))
    (fun i => (hmass i).trans (by dsimp only [S, sampledMemberInputBudget]; omega))
    (fun i => (hvalue i).trans hBS)
  refine ⟨hmember.1, ?_⟩
  change mass.2 + rounded.2 + values.2 + connection.2 +
    (countedGroupMemberWithWork Q b scales connection.1 mass.1 values.1 draw).2 + 5 ≤ _
  unfold sampledMemberBitBudget
  dsimp only [S] at hmember
  omega

end BinaryFraction
end EditApproximation

end OAI
