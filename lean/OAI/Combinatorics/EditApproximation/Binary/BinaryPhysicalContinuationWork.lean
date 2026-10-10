import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedActionStorage
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalWarmupKernel

namespace OAI

/-! Actual endpoint distances and connection words supply all representation
premises of the two Bellman scans and final refinement update. -/

namespace EditApproximation
namespace BinaryFraction

def physicalContinuationInputBudget (M B : ℕ) : ℕ :=
  B + connectionWordBudget M B + endpointDistanceWordBudget B + 4 * B + 2

def physicalContinuationBitBudget (M P nr ng no B : ℕ) : ℕ :=
  wideActionsBitBudget M P nr B + 2000 * (B + 1) ^ 2 +
    localContinuationBitBudget M (nr * (40 * P + 2) ^ (2 * M)) ng no
      (physicalContinuationInputBudget M B) (endpointDistanceBitBudget B) + 1

private theorem endpointDistance_uniform {n : ℕ} (q r : TargetInterval n) (B : ℕ)
    (hn : Nat.size n + 2 ≤ B) :
    (endpointDistanceWithWork q r).1.width ≤ endpointDistanceWordBudget B ∧
      (endpointDistanceWithWork q r).2 ≤ endpointDistanceBitBudget B :=
  endpointDistanceWithWork_bounds q r B
    ((Nat.add_le_add_right (Nat.size_le_size (q.ordered.trans q.valid)) 2).trans hn)
    ((Nat.add_le_add_right (Nat.size_le_size q.valid) 2).trans hn)
    ((Nat.add_le_add_right (Nat.size_le_size (r.ordered.trans r.valid)) 2).trans hn)
    ((Nat.add_le_add_right (Nat.size_le_size r.valid) 2).trans hn)

theorem physicalContinuationWithWork_bounds {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P F B : ℕ)
    (delta fallback : BinaryFraction) (old current : Fin M × TargetInterval ny → BinaryFraction)
    (groups online : List (BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (query : TargetInterval ny) (hPpos : 0 < P) (hB : 10 ≤ B)
    (hnx : Nat.size nx ≤ B) (hny : Nat.size ny + 2 ≤ B)
    (hM : Nat.size M ≤ B) (hP : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hrep : ∀ br ∈ representatives, Nat.size br.1 ≤ B)
    (hdelta : delta.width ≤ B) (hfallback : fallback.width ≤ B)
    (hold : ∀ s, (old s).width ≤ B) (hcurrent : ∀ s, (current s).width ≤ B)
    (hgroups : ∀ action ∈ groups, action.connection.width ≤ connectionWordBudget M B)
    (honline : ∀ action ∈ online, action.connection.width ≤ connectionWordBudget M B) :
    (physicalContinuationWithWork parent representatives P F delta fallback old current groups online query).1.width ≤
        localContinuationWordBudget M (physicalContinuationInputBudget M B) ∧
      (physicalContinuationWithWork parent representatives P F delta fallback old current groups online query).2 ≤
        physicalContinuationBitBudget M P representatives.length groups.length online.length B := by
  let wide := wideActionsFromRepresentativesWithWork M parent representatives P
  let L := canonicalMulWithWork (nat 128) (nat F)
  let W := physicalContinuationInputBudget M B
  have hBW : B ≤ W := by dsimp only [W, physicalContinuationInputBudget]; omega
  have h128 : (nat 128).width ≤ B :=
    (nat_width_le 128).trans (by change 10 ≤ B; exact hB)
  have hL := canonicalMulWithWork_width (nat 128) (nat F) B h128 ((nat_width_le F).trans hF)
  have hLc := canonicalMulWithWork_cost (nat 128) (nat F) B h128 ((nat_width_le F).trans hF)
  have hw := wideActionsFromRepresentativesWithWork_bounds parent representatives P B
    hPpos hnx hny hM hP hrep
  have htail := localContinuationWithWork_bounds endpointDistanceWithWork L.1 delta fallback
    old current query wide.1 groups online W (endpointDistanceBitBudget B)
    (hL.trans (by dsimp only [W, physicalContinuationInputBudget]; omega))
    (hdelta.trans hBW) (hfallback.trans hBW)
    (fun action _ => (endpointDistance_uniform query action.center B hny).1.trans (by
      dsimp only [W, physicalContinuationInputBudget]; omega))
    (fun action _ => (endpointDistance_uniform query action.center B hny).2)
    (by
      intro action ha
      rcases List.mem_append.mp ha with ha | ha
      · rcases List.mem_append.mp ha with ha | ha
        · exact (hw.2.1 action ha).trans (by dsimp only [W, physicalContinuationInputBudget]; omega)
        · exact (hgroups action ha).trans (by dsimp only [W, physicalContinuationInputBudget]; omega)
      · exact (honline action ha).trans (by dsimp only [W, physicalContinuationInputBudget]; omega))
    (fun action _ i => (hold (action.childState i)).trans hBW)
    (fun action _ i => (hcurrent (action.childState i)).trans hBW)
  refine ⟨htail.1, ?_⟩
  have htailCost := htail.2.trans (show
      localContinuationBitBudget M wide.1.length groups.length online.length W (endpointDistanceBitBudget B) ≤
      localContinuationBitBudget M (representatives.length * (40 * P + 2) ^ (2 * M)) groups.length online.length W
        (endpointDistanceBitBudget B) by
    unfold localContinuationBitBudget bellmanBitBudget
    gcongr <;> exact hw.1)
  change wide.2 + L.2 +
    (localContinuationWithWork endpointDistanceWithWork L.1 delta fallback old current query wide.1 groups online).2 + 1 ≤ _
  have hwc := hw.2.2
  change wide.2 ≤ _ at hwc
  change L.2 ≤ _ at hLc
  unfold physicalContinuationBitBudget
  change _ ≤ wideActionsBitBudget M P representatives.length B + 2000 * (B + 1) ^ 2 +
    localContinuationBitBudget M (representatives.length * (40 * P + 2) ^ (2 * M))
      groups.length online.length W (endpointDistanceBitBudget B) + 1
  omega

end BinaryFraction
end EditApproximation

end OAI
