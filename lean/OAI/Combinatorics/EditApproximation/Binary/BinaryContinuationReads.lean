import OAI.Combinatorics.EditApproximation.Binary.BinaryBellmanReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryCachedContinuation
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Both Bellman minima and the online score list execute their table
lookups before evaluating the final stored-fraction decrement. -/

namespace EditApproximation
namespace BinaryFraction



theorem localContinuationReadWithWork_eq_cost {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L delta fallback : BinaryFraction)
    (old current : Child → BinaryFraction × ℕ) (query : Parent)
    (wide groups online : List (BinaryBellmanAction Parent Child M)) (R : ℕ)
    (ho : ∀ s, (old s).2 ≤ R) (hn : ∀ s, (current s).2 ≤ R) :
    (localContinuationReadWithWork distance L delta fallback old current query wide groups online).1 =
      (localContinuationWithWork distance L delta fallback (fun s => (old s).1)
        (fun s => (current s).1) query wide groups online).1 ∧
    (localContinuationReadWithWork distance L delta fallback old current query wide groups online).2 ≤
      (localContinuationWithWork distance L delta fallback (fun s => (old s).1)
        (fun s => (current s).1) query wide groups online).2 +
        (wide.length + groups.length + online.length) * (M * (R + 3)) := by
  have hwv := bellmanReadWithWork_eq distance L fallback old query wide
  have hwc := bellmanReadWithWork_cost distance L fallback old query wide R (fun _ _ _ => ho _)
  have hgv := bellmanReadWithWork_eq distance L
    (bellmanWithWork distance L fallback (fun s => (old s).1) query wide).1 current query groups
  have hgc := bellmanReadWithWork_cost distance L
    (bellmanWithWork distance L fallback (fun s => (old s).1) query wide).1 current query groups R
    (fun _ _ _ => hn _)
  have hs := arithmeticMapWithWork_extra
    (bellmanActionReadWithWork distance L current query)
    (bellmanActionWithWork distance L (fun s => (current s).1) query)
    (fun _ => M * (R + 3)) online
    (fun a _ => bellmanActionReadWithWork_eq distance L current query a)
    (fun a _ => bellmanActionReadWithWork_cost distance L current query a R (fun _ => hn _))
  have hsum : (online.map (fun _ => M * (R + 3))).sum = online.length * (M * (R + 3)) := by
    simp only [List.map_const', List.sum_replicate, smul_eq_mul]
  rw [hsum] at hs
  unfold localContinuationReadWithWork localContinuationWithWork
  dsimp only
  rw [hwv, hgv, hs.1]
  exact ⟨rfl, by nlinarith only [hwc, hgc, hs.2]⟩



theorem physicalContinuationReadWithWork_eq_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P F : ℕ)
    (delta fallback : BinaryFraction)
    (old current : Fin M × TargetInterval ny → BinaryFraction × ℕ)
    (groups online : List (BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (query : TargetInterval ny) (R : ℕ) (ho : ∀ s, (old s).2 ≤ R) (hn : ∀ s, (current s).2 ≤ R) :
    (physicalContinuationReadWithWork parent representatives P F delta fallback old current groups online query).1 =
      (physicalContinuationWithWork parent representatives P F delta fallback
        (fun s => (old s).1) (fun s => (current s).1) groups online query).1 ∧
    (physicalContinuationReadWithWork parent representatives P F delta fallback old current groups online query).2 ≤
      (physicalContinuationWithWork parent representatives P F delta fallback
        (fun s => (old s).1) (fun s => (current s).1) groups online query).2 +
      ((wideActionsFromRepresentativesWithWork M parent representatives P).1.length +
        groups.length + online.length) * (M * (R + 3)) := by
  have h := localContinuationReadWithWork_eq_cost endpointDistanceWithWork
    (canonicalMulWithWork (nat 128) (nat F)).1 delta fallback old current query
    (wideActionsFromRepresentativesWithWork M parent representatives P).1 groups online R ho hn
  unfold physicalContinuationReadWithWork physicalContinuationWithWork
  dsimp only
  exact ⟨h.1, by omega⟩

end BinaryFraction
end EditApproximation

end OAI
