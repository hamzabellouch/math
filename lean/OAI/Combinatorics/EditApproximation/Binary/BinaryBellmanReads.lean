import OAI.Combinatorics.EditApproximation.Binary.BinaryBellmanKernel
import OAI.Combinatorics.EditApproximation.Binary.BinaryReadComposition
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Bellman action evaluation with literal finite-table reader calls.
Child words are gathered once, then Boolean arithmetic
operates on that stored list. Reader scans are part of the returned cost. -/

namespace EditApproximation
namespace BinaryFraction



theorem bellmanActionReadWithWork_eq {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L : BinaryFraction)
    (read : Child → BinaryFraction × ℕ) (query : Parent)
    (action : BinaryBellmanAction Parent Child M) :
    (bellmanActionReadWithWork distance L read query action).1 =
      (bellmanActionWithWork distance L (fun s => (read s).1) query action).1 := by
  simp only [bellmanActionReadWithWork, arithmeticMapWithWork_value,
    bellmanActionWithWork, List.ofFn_eq_map]

theorem bellmanActionReadWithWork_cost {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L : BinaryFraction)
    (read : Child → BinaryFraction × ℕ) (query : Parent)
    (action : BinaryBellmanAction Parent Child M) (R : ℕ)
    (hread : ∀ i, (read (action.childState i)).2 ≤ R) :
    (bellmanActionReadWithWork distance L read query action).2 ≤
      (bellmanActionWithWork distance L (fun s => (read s).1) query action).2 + M * (R + 3) := by
  have h := arithmeticMapWithWork_cost (fun i => read (action.childState i))
    (List.finRange M) R (fun i _ => hread i)
  simp only [List.length_finRange] at h
  simp only [bellmanActionReadWithWork, arithmeticMapWithWork_value,
    bellmanActionWithWork, List.ofFn_eq_map]
  omega



theorem bellmanReadWithWork_eq {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L fallback : BinaryFraction)
    (read : Child → BinaryFraction × ℕ) (query : Parent)
    (actions : List (BinaryBellmanAction Parent Child M)) :
    (bellmanReadWithWork distance L fallback read query actions).1 =
      (bellmanWithWork distance L fallback (fun s => (read s).1) query actions).1 := by
  simp only [bellmanReadWithWork, bellmanWithWork, arithmeticMapWithWork_value,
    bellmanActionReadWithWork_eq]

theorem bellmanReadWithWork_cost {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L fallback : BinaryFraction)
    (read : Child → BinaryFraction × ℕ) (query : Parent)
    (actions : List (BinaryBellmanAction Parent Child M)) (R : ℕ)
    (hread : ∀ action ∈ actions, ∀ i, (read (action.childState i)).2 ≤ R) :
    (bellmanReadWithWork distance L fallback read query actions).2 ≤
      (bellmanWithWork distance L fallback (fun s => (read s).1) query actions).2 +
        actions.length * (M * (R + 3)) := by
  have h := arithmeticMapWithWork_extra
    (bellmanActionReadWithWork distance L read query)
    (bellmanActionWithWork distance L (fun s => (read s).1) query)
    (fun _ => M * (R + 3)) actions
    (fun action _ => bellmanActionReadWithWork_eq distance L read query action)
    (fun action ha => bellmanActionReadWithWork_cost distance L read query action R (hread action ha))
  have hs : (actions.map (fun _ => M * (R + 3))).sum = actions.length * (M * (R + 3)) := by
    simp only [List.map_const', List.sum_replicate, smul_eq_mul]
  rw [hs] at h
  unfold bellmanReadWithWork bellmanWithWork
  dsimp only
  rw [h.1]
  omega

theorem bellmanWithWork_action_count {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → BinaryFraction × ℕ) (L fallback : BinaryFraction)
    (child : Child → BinaryFraction) (query : Parent)
    (actions : List (BinaryBellmanAction Parent Child M)) :
    actions.length ≤ (bellmanWithWork distance L fallback child query actions).2 := by
  have h := arithmeticMapWithWork_length_le_cost
    (bellmanActionWithWork distance L child query) actions
  change actions.length ≤ _ + _ + 1
  omega

end BinaryFraction
end EditApproximation

end OAI
