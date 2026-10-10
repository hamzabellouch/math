import OAI.Combinatorics.EditApproximation.Binary.BinaryBellmanKernel

namespace OAI

/-! Bit costs for the full numerical tail after its finite candidate lists
have been prepared. Both Bellman minima, the online score minimum, and the
final clipped decrement are executed by the counter being bounded. -/

namespace EditApproximation
namespace BinaryFraction

def localContinuationInputBudget (M B : ℕ) : ℕ :=
  B + 2 * bellmanActionWordBudget M B + 1

def localContinuationWordBudget (M B : ℕ) : ℕ :=
  refinementUpdateWordBudget (localContinuationInputBudget M B)

def localContinuationBitBudget (M nw ng no B C : ℕ) : ℕ :=
  bellmanBitBudget M nw B B C +
  bellmanBitBudget M ng B (B + bellmanActionWordBudget M B) C +
  no * (bellmanActionBitBudget M B C + 3) +
  (2 + no * (1000 * (bellmanActionWordBudget M B + 1) ^ 2 + 2)) +
  refinementUpdateBitBudget (localContinuationInputBudget M B) + 3

theorem localContinuationWithWork_bounds {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L delta fallback : BinaryFraction)
    (old current : Child → BinaryFraction) (query : Parent)
    (wide groups online : List (BinaryBellmanAction Parent Child M)) (B C : ℕ)
    (hL : L.width ≤ B) (hdelta : delta.width ≤ B) (hf : fallback.width ≤ B)
    (hd : ∀ action ∈ wide ++ groups ++ online, (distance query action.center).1.width ≤ B)
    (hdc : ∀ action ∈ wide ++ groups ++ online, (distance query action.center).2 ≤ C)
    (hc : ∀ action ∈ wide ++ groups ++ online, action.connection.width ≤ B)
    (ho : ∀ action ∈ wide, ∀ i, (old (action.childState i)).width ≤ B)
    (hn : ∀ action ∈ groups ++ online, ∀ i, (current (action.childState i)).width ≤ B) :
    (localContinuationWithWork distance L delta fallback old current query wide groups online).1.width ≤
        localContinuationWordBudget M B ∧
      (localContinuationWithWork distance L delta fallback old current query wide groups online).2 ≤
        localContinuationBitBudget M wide.length groups.length online.length B C := by
  let warm := bellmanWithWork distance L fallback old query wide
  let cone := bellmanWithWork distance L warm.1 current query groups
  let scores := arithmeticMapWithWork (bellmanActionWithWork distance L current query) online
  let onlineMin := onlineMinimumWithWork scores.1
  have hw := bellmanWithWork_bounds distance L fallback old query wide B B C hL hf
    (fun a ha => hd a (by simp [ha]))
    (fun a ha => hdc a (by simp [ha]))
    (fun a ha => hc a (by simp [ha])) ho
  have hg := bellmanWithWork_bounds distance L warm.1 current query groups B
    (B + bellmanActionWordBudget M B) C hL hw.1
    (fun a ha => hd a (by simp [ha]))
    (fun a ha => hdc a (by simp [ha]))
    (fun a ha => hc a (by simp [ha]))
    (fun a ha => hn a (List.mem_append_left online ha))
  have hs (a : BinaryBellmanAction Parent Child M) (ha : a ∈ online) :=
    bellmanActionWithWork_bounds distance L current query a B C hL
      (hd a (by simp [ha])) (hdc a (by simp [ha]))
      (hc a (by simp [ha])) (hn a (List.mem_append_right groups ha))
  have hsw : ∀ value ∈ scores.1, value.width ≤ bellmanActionWordBudget M B := by
    intro value hvalue
    simp only [scores, arithmeticMapWithWork_value] at hvalue
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hvalue
    exact (hs a ha).1
  have hsc := arithmeticMapWithWork_cost (bellmanActionWithWork distance L current query) online
    (bellmanActionBitBudget M B C) (fun a ha => (hs a ha).2)
  have hom := onlineMinimumWithWork_bounds scores.1 (bellmanActionWordBudget M B) hsw
  have hlen : scores.1.length = online.length := by
    simp only [scores, arithmeticMapWithWork_value, List.length_map]
  rw [hlen] at hom
  have hinput : 1 ≤ localContinuationInputBudget M B := by
    unfold localContinuationInputBudget
    omega
  have hdelta' : delta.width ≤ localContinuationInputBudget M B := hdelta.trans (by
    unfold localContinuationInputBudget; omega)
  have hcone : cone.1.width ≤ localContinuationInputBudget M B := hg.1.trans (by
    unfold localContinuationInputBudget; omega)
  have honline : ∀ value ∈ onlineMin.1, value.width ≤ localContinuationInputBudget M B := by
    intro value hv
    exact (hom.1 value hv).trans (by unfold localContinuationInputBudget; omega)
  have hresult := refinementUpdateWithWork_bounds delta cone.1 onlineMin.1
    (localContinuationInputBudget M B) hinput hdelta' hcone honline
  refine ⟨hresult.1, ?_⟩
  change warm.2 + cone.2 + scores.2 + onlineMin.2 +
    (refinementUpdateWithWork delta cone.1 onlineMin.1).2 + 3 ≤ _
  have hwc := hw.2
  have hgc := hg.2
  change warm.2 ≤ _ at hwc
  change cone.2 ≤ _ at hgc
  change scores.2 ≤ _ at hsc
  have homc := hom.2
  change onlineMin.2 ≤ _ at homc
  unfold localContinuationBitBudget
  omega

end BinaryFraction
end EditApproximation

end OAI
