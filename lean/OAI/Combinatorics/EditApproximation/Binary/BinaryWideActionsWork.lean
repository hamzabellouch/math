import OAI.Combinatorics.EditApproximation.Binary.BinaryPhysicalContinuation
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedRepresentativeWork

namespace OAI

/-! The full wide-action list materializes each grid and each connection
charge. Endpoint representation bounds follow from the interval subtype. -/

namespace EditApproximation
namespace BinaryFraction

theorem endpointActionWithWork_bounds {n M : ℕ} (center : TargetInterval n)
    (states : Fin M → TargetInterval n) (B : ℕ) (hn : Nat.size n + 2 ≤ B) :
    (endpointActionWithWork center states).1.connection.width ≤ connectionWordBudget M B ∧
      (endpointActionWithWork center states).2 ≤ connectionBitBudget M B + 2 * B + 2 * M + 3 := by
  have hlo : (nat center.lo).width ≤ B := (nat_width_le center.lo).trans
    ((Nat.add_le_add_right (Nat.size_le_size (center.ordered.trans center.valid)) 2).trans hn)
  have hhi : (nat center.hi).width ≤ B := (nat_width_le center.hi).trans
    ((Nat.add_le_add_right (Nat.size_le_size center.valid) 2).trans hn)
  have hs : ∀ q ∈ List.ofFn states, Nat.size q.lo + 2 ≤ B ∧ Nat.size q.hi + 2 ≤ B := by
    intro q _
    exact ⟨(Nat.add_le_add_right (Nat.size_le_size (q.ordered.trans q.valid)) 2).trans hn,
      (Nat.add_le_add_right (Nat.size_le_size q.valid) 2).trans hn⟩
  have hw := connectionWithWork_width (nat center.lo) (nat center.hi) (List.ofFn states) B hlo hhi hs
  have hc := connectionWithWork_cost (nat center.lo) (nat center.hi) (List.ofFn states) B hlo hhi hs
  simp only [List.length_ofFn] at hw hc
  constructor
  · exact hw
  · have hlo' := (Nat.size_le_size (center.ordered.trans center.valid)).trans (show Nat.size n ≤ B by omega)
    have hhi' := (Nat.size_le_size center.valid).trans (show Nat.size n ≤ B by omega)
    change (connectionWithWork (nat center.lo) (nat center.hi) (List.ofFn states)).2 +
      Nat.size center.lo + Nat.size center.hi + M + 2 + M + 1 ≤ _
    omega

def wideActionsBitBudget (M P count B : ℕ) : ℕ :=
  let V := (40 * P + 2) ^ (2 * M)
  count * (wideMaterializationBitBudget M P B +
    V * (connectionBitBudget M B + 2 * B + 2 * M + 6) + 1 + V + 3)

theorem wideActionsFromRepresentativesWithWork_bounds {nx ny M : ℕ}
    (parent : TargetInterval nx) (representatives : List (ℕ × TargetInterval ny)) (P B : ℕ)
    (hPpos : 0 < P) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny + 2 ≤ B)
    (hM : Nat.size M ≤ B) (hP : Nat.size P ≤ B)
    (hrep : ∀ br ∈ representatives, Nat.size br.1 ≤ B) :
    (wideActionsFromRepresentativesWithWork M parent representatives P).1.length ≤
        representatives.length * (40 * P + 2) ^ (2 * M) ∧
      (∀ action ∈ (wideActionsFromRepresentativesWithWork M parent representatives P).1,
        action.connection.width ≤ connectionWordBudget M B) ∧
      (wideActionsFromRepresentativesWithWork M parent representatives P).2 ≤
        wideActionsBitBudget M P representatives.length B := by
  let V := (40 * P + 2) ^ (2 * M)
  let callback := fun br : ℕ × TargetInterval ny =>
    let grids := wideActionGridWithWork M parent br.2 br.1 P
    let actions := arithmeticMapWithWork (fun states => endpointActionWithWork br.2 states.get) grids.1
    (actions.1, grids.2 + actions.2 + 1)
  have hlen (br : ℕ × TargetInterval ny) : (wideActionGridWithWork M parent br.2 br.1 P).1.length ≤ V := by
    have hh := congrArg List.length (wideActionGridWithWork_value M parent br.2 br.1 P hPpos)
    simp only [List.length_map] at hh
    rw [hh]
    exact wideActionList_length_le M parent br.2 br.1 P hPpos
  have hc (br : ℕ × TargetInterval ny) (hbr : br ∈ representatives) :
      (callback br).2 ≤ wideMaterializationBitBudget M P B +
        V * (connectionBitBudget M B + 2 * B + 2 * M + 6) + 1 := by
    have hg := wideActionGridWithWork_complete_cost M parent br.2 br.1 P B hPpos hnx
      (by omega) hM (hrep br hbr) hP
    have hm := arithmeticMapWithWork_cost
      (fun states : Vector (TargetInterval ny) M => endpointActionWithWork br.2 states.get)
      (wideActionGridWithWork M parent br.2 br.1 P).1
      (connectionBitBudget M B + 2 * B + 2 * M + 3)
      (fun states _ => (endpointActionWithWork_bounds br.2 states.get B hny).2)
    have hm' := hm.trans (Nat.mul_le_mul_right _ (hlen br))
    change (wideActionGridWithWork M parent br.2 br.1 P).2 + _ + 1 ≤ _
    simp only [Nat.add_assoc, Nat.reduceAdd] at hm' ⊢
    omega
  have hl (br : ℕ × TargetInterval ny) : (callback br).1.length ≤ V := by
    simpa only [callback, arithmeticMapWithWork_value, List.length_map] using hlen br
  have hcost := arithmeticFlatMapWithWork_cost callback representatives
    (wideMaterializationBitBudget M P B + V * (connectionBitBudget M B + 2 * B + 2 * M + 6) + 1)
    V hc (fun br _ => hl br)
  have hlength : (representatives.flatMap (fun br => (callback br).1)).length ≤ representatives.length * V :=
    list_flatMap_length_le representatives (fun br => (callback br).1) V (fun br _ => hl br)
  refine ⟨?_, ?_, hcost⟩
  · simpa only [wideActionsFromRepresentativesWithWork, arithmeticFlatMapWithWork_value] using hlength
  · intro action ha
    simp only [wideActionsFromRepresentativesWithWork, arithmeticFlatMapWithWork_value,
      arithmeticMapWithWork_value] at ha
    obtain ⟨br, _, ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨states, _, rfl⟩ := List.mem_map.mp ha
    exact (endpointActionWithWork_bounds br.2 states.get B hny).1

end BinaryFraction
end EditApproximation

end OAI
