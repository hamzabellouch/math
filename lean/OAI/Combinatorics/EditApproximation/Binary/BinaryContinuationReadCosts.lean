import OAI.Combinatorics.EditApproximation.Binary.BinaryReadCostBounds
import OAI.Combinatorics.EditApproximation.Binary.BinaryContinuationReads

namespace OAI

/-! Continuation cost transfer includes both Bellman scans and the
literal online score array, with each child lookup charged. -/

namespace EditApproximation
namespace BinaryFraction

theorem bellmanActionReadWithWork_factor {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L : BinaryFraction)
    (read : Child → BinaryFraction × ℕ) (query : Parent)
    (action : BinaryBellmanAction Parent Child M) (R : ℕ)
    (hr : ∀ i, (read (action.childState i)).2 ≤ R) :
    (bellmanActionReadWithWork distance L read query action).2 ≤
      (bellmanActionWithWork distance L (fun s => (read s).1) query action).2 * tableReadFactor R := by
  apply tableReadFactor_absorb _ _ M R
    (bellmanActionReadWithWork_cost distance L read query action R hr)
  have hs : M ≤ (sumListWithWork (List.ofFn fun i => (read (action.childState i)).1)).2 := by
    simp only [sumListWithWork, List.length_ofFn]
    omega
  unfold bellmanActionWithWork
  dsimp only
  omega

theorem bellmanReadWithWork_factor {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L fallback : BinaryFraction)
    (read : Child → BinaryFraction × ℕ) (query : Parent)
    (actions : List (BinaryBellmanAction Parent Child M)) (R : ℕ)
    (hr : ∀ action ∈ actions, ∀ i, (read (action.childState i)).2 ≤ R) :
    (bellmanReadWithWork distance L fallback read query actions).2 ≤
      (bellmanWithWork distance L fallback (fun s => (read s).1) query actions).2 * tableReadFactor R := by
  have hs := arithmeticMapWithWork_factor
    (bellmanActionReadWithWork distance L read query)
    (bellmanActionWithWork distance L (fun s => (read s).1) query)
    actions (tableReadFactor R) (tableReadFactor_pos R)
    (fun action _ => bellmanActionReadWithWork_eq distance L read query action)
    (fun action ha => bellmanActionReadWithWork_factor distance L read query action R (hr action ha))
  unfold bellmanReadWithWork bellmanWithWork
  dsimp only
  rw [hs.1]
  apply cost_replace_factor _ _ _ _ _ hs.2 (tableReadFactor_pos R) <;> omega

theorem localContinuationReadWithWork_factor {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L delta fallback : BinaryFraction)
    (old current : Child → BinaryFraction × ℕ) (query : Parent)
    (wide groups online : List (BinaryBellmanAction Parent Child M)) (R : ℕ)
    (ho : ∀ s, (old s).2 ≤ R) (hn : ∀ s, (current s).2 ≤ R) :
    (localContinuationReadWithWork distance L delta fallback old current query wide groups online).2 ≤
      (localContinuationWithWork distance L delta fallback (fun s => (old s).1)
        (fun s => (current s).1) query wide groups online).2 * tableReadFactor R := by
  have hw := bellmanReadWithWork_factor distance L fallback old query wide R (fun _ _ _ => ho _)
  have hwq := bellmanReadWithWork_eq distance L fallback old query wide
  have hg := bellmanReadWithWork_factor distance L
    (bellmanWithWork distance L fallback (fun s => (old s).1) query wide).1 current query groups R
    (fun _ _ _ => hn _)
  have hgq := bellmanReadWithWork_eq distance L
    (bellmanWithWork distance L fallback (fun s => (old s).1) query wide).1 current query groups
  have hs := arithmeticMapWithWork_factor
    (bellmanActionReadWithWork distance L current query)
    (bellmanActionWithWork distance L (fun s => (current s).1) query)
    online (tableReadFactor R) (tableReadFactor_pos R)
    (fun action _ => bellmanActionReadWithWork_eq distance L current query action)
    (fun action _ => bellmanActionReadWithWork_factor distance L current query action R (fun _ => hn _))
  have h := Nat.add_le_add (Nat.add_le_add hw hg) hs.2
  simp only [← Nat.add_mul] at h
  unfold localContinuationReadWithWork localContinuationWithWork
  dsimp only
  rw [hwq, hgq, hs.1]
  apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

theorem physicalContinuationReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval n)) (P F : ℕ)
    (delta fallback : BinaryFraction) (old current : Fin M × TargetInterval n → BinaryFraction × ℕ)
    (groups online : List (BinaryBellmanAction (TargetInterval n) (Fin M × TargetInterval n) M))
    (query : TargetInterval n) (R : ℕ) (ho : ∀ s, (old s).2 ≤ R) (hn : ∀ s, (current s).2 ≤ R) :
    (physicalContinuationReadWithWork parent representatives P F delta fallback old current groups online query).2 ≤
      (physicalContinuationWithWork parent representatives P F delta fallback
        (fun s => (old s).1) (fun s => (current s).1) groups online query).2 * tableReadFactor R := by
  have h := localContinuationReadWithWork_factor endpointDistanceWithWork
    (canonicalMulWithWork (nat 128) (nat F)).1 delta fallback old current query
    (wideActionsFromRepresentativesWithWork M parent representatives P).1 groups online R ho hn
  unfold physicalContinuationReadWithWork physicalContinuationWithWork
  dsimp only
  apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

end BinaryFraction
end EditApproximation

end OAI
