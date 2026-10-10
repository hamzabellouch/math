import OAI.Combinatorics.EditApproximation.Binary.BinarySampledGroupWork

namespace OAI

/-! Complete group selection cost, including every sampled member estimate
and reconstruction of the selected rounded action. -/

namespace EditApproximation
namespace BinaryFraction

private theorem roundedBandBitBudget_mono_vertices (e b M v w B : ℕ) (h : v ≤ w) :
    roundedBandBitBudget e b M v B ≤ roundedBandBitBudget e b M w B := by
  unfold roundedBandBitBudget bandEnvelopeBitBudget
  dsimp only
  gcongr

private theorem sampledMemberBitBudget_mono_vertices (M T e b v w B : ℕ) (h : v ≤ w) :
    sampledMemberBitBudget M T e b v B ≤ sampledMemberBitBudget M T e b w B := by
  have hr := roundedBandBitBudget_mono_vertices e b M v w B h
  unfold sampledMemberBitBudget bandEnvelopeBitBudget
  dsimp only
  gcongr

def selectedGroupBitBudget (M T e b members vertices B : ℕ) : ℕ :=
  members * (sampledMemberBitBudget M T e b vertices B +
    1000 * (sampledMemberWordBudget M T b B + 1) ^ 2 + 3) + 1 +
    roundedBandBitBudget e b M vertices B + connectionBitBudget M B + 2 * B + 2 * M + 6

theorem sampledGroupActionWithWork_cost {α : Type*} (source target : List α) {M T : ℕ}
    (parent : TargetInterval source.length) (b P exponent Q : ℕ) (tau F : BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (scales : Fin T → BinaryFraction)
    (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)
    (members : List (UnskippedBand source target parent b P exponent tau.value F.value
      (fun i q => (child i q).value) (fun i q => (initial i q).value))) (hne : members ≠ [])
    (V B : ℕ) (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B)
    (hb : Nat.size b + 2 ≤ B) (hny : Nat.size target.length + 2 ≤ B)
    (hs : ∀ t, (scales t).width ≤ B)
    (hV : ∀ member ∈ members, member.actions.length ≤ V)
    (hi : ∀ member ∈ members, ∀ action ∈ member.actions, ∀ i, (initial i (action i)).width ≤ B)
    (hv : ∀ i q, (current i q).width ≤ B) :
    (sampledGroupActionWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).2 ≤ selectedGroupBitBudget M T exponent b members.length V B := by
  let estimate := unskippedEstimateWithWork source target parent b P exponent Q tau F
    child initial current scales draw
  have he (member) (hm : member ∈ members) := unskippedEstimateWithWork_bounds source target parent b P exponent Q
    tau F child initial current scales draw member B hM hQ hb hny hs (hi member hm) hv
  have hselection := selectGroupWithWork_cost members hne estimate
    (sampledMemberBitBudget M T exponent b V B) (sampledMemberWordBudget M T b B)
    (fun member hm => (he member hm).2.trans (sampledMemberBitBudget_mono_vertices _ _ _ _ _ _ _ (hV member hm)))
    (fun member hm => (he member hm).1)
  let selected := (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F
    child initial current scales draw members hne).1
  have hselected : selected ∈ members := by
    rw [show selected = selectGroupMember members hne (fun member => (estimate member).1.value) from
      selectGroupWithWork_value members hne estimate]
    exact (selectGroupMember_spec members hne _).1
  have hrounded := (roundedBandWithWork_cost exponent b selected.actions selected.nonempty initial B
    (by omega) (hi selected hselected)).trans
      (roundedBandBitBudget_mono_vertices _ _ _ _ _ _ (hV selected hselected))
  let states := (roundedBandWithWork exponent b selected.actions selected.nonempty initial).1.get
  have hcenterlo : Nat.size selected.center.lo + 2 ≤ B :=
    (Nat.add_le_add_right (Nat.size_le_size (selected.center.ordered.trans selected.center.valid)) 2).trans hny
  have hcenterhi : Nat.size selected.center.hi + 2 ≤ B :=
    (Nat.add_le_add_right (Nat.size_le_size selected.center.valid) 2).trans hny
  have hstates : ∀ s ∈ List.ofFn states, Nat.size s.lo + 2 ≤ B ∧ Nat.size s.hi + 2 ≤ B := by
    intro s _
    exact ⟨(Nat.add_le_add_right (Nat.size_le_size (s.ordered.trans s.valid)) 2).trans hny,
      (Nat.add_le_add_right (Nat.size_le_size s.valid) 2).trans hny⟩
  have hconnection := connectionWithWork_cost (nat selected.center.lo) (nat selected.center.hi)
    (List.ofFn states) B ((nat_width_le _).trans hcenterlo)
      ((nat_width_le _).trans hcenterhi) hstates
  simp only [List.length_ofFn] at hconnection
  have haction : (endpointActionWithWork selected.center states).2 ≤
      connectionBitBudget M B + 2 * B + 2 * M + 3 := by
    change (connectionWithWork (nat selected.center.lo) (nat selected.center.hi) (List.ofFn states)).2 +
      Nat.size selected.center.lo + Nat.size selected.center.hi + M + 2 + M + 1 ≤ _
    omega
  change (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child initial current
    scales draw members hne).2 +
    (roundedBandWithWork exponent b selected.actions selected.nonempty initial).2 +
    (endpointActionWithWork selected.center states).2 + 3 ≤ _
  change (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child initial current
    scales draw members hne).2 ≤ _ at hselection
  unfold selectedGroupBitBudget
  omega

end BinaryFraction
end EditApproximation

end OAI
