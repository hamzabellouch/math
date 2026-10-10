import OAI.Combinatorics.EditApproximation.Geometry.TreeParameters
import OAI.Combinatorics.EditApproximation.Geometry.StateGeometry

namespace OAI

/-!
# Counting the actual labeled state domain

The count includes repeated interval labels at different physical nodes.
It bounds simultaneous seed/amplification events without identifying those
nodes or replacing the finite target-state loops by an oracle.
-/

namespace EditApproximation

open Finset

theorem list_flatMap_length_le {α β : Type*} (entries : List α) (f : α → List β)
    (K : ℕ) (h : ∀ a ∈ entries, (f a).length ≤ K) :
    (entries.flatMap f).length ≤ entries.length * K := by
  induction entries with
  | nil => simp
  | cons a rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have ha := h a (by simp)
    have hrest := ih (fun b hb => h b (by simp [hb]))
    nlinarith

theorem targetStates_length_le (n : ℕ) : (targetStates n).length ≤ (n + 1) ^ 2 := by
  unfold targetStates
  have h := list_flatMap_length_le (List.range (n + 1))
    (fun lo => (List.range (n + 1)).filterMap fun hi => makeTargetState n lo hi)
    (n + 1) (by
      intro lo hlo
      simpa only [List.length_range] using
        List.length_filterMap_le (fun hi => makeTargetState n lo hi) (List.range (n + 1)))
  simpa only [List.length_range, pow_two] using h

def labeledStateCount (M nx ny : ℕ) : ℕ :=
  (∑ d ∈ range (intervalTreeDepth M nx + 1), Fintype.card (TreeLayer M d)) *
    (targetStates ny).length

theorem labeledStateCount_le (M nx ny : ℕ) (hM : 2 ≤ M) :
    labeledStateCount M nx ny ≤ 2 * M * max 1 nx * (ny + 1) ^ 2 := by
  exact Nat.mul_le_mul (intervalTreeDepth_node_count M nx hM) (targetStates_length_le ny)

theorem computed_labeledStateCount_le (N nx ny : ℕ) (hN : 0 < N)
    (hnx : nx ≤ N) (hny : ny ≤ N) (hell : 200 ≤ inputSmallLog N) :
    labeledStateCount (integerParameters N).M nx ny ≤ 2 ^ (5 * inputHeight N) := by
  have hbranch := computed_branching_bounds N hN hell
  have hM : (integerParameters N).M ≤ 2 ^ inputHeight N :=
    pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hbranch.2.2
  have hx : max 1 nx ≤ 2 ^ inputHeight N := by
    apply max_le Nat.one_le_two_pow
    exact hnx.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N))
  have hy : ny + 1 ≤ 2 ^ inputHeight N :=
    (by omega : ny + 1 ≤ N + 2).trans (inputHeight_covers_length N)
  have hproduct : 2 * (integerParameters N).M * max 1 nx * (ny + 1) ^ 2 ≤
      2 * 2 ^ inputHeight N * 2 ^ inputHeight N * (2 ^ inputHeight N) ^ 2 := by
    gcongr
  have hidentity : 2 * 2 ^ inputHeight N * 2 ^ inputHeight N * (2 ^ inputHeight N) ^ 2 =
      2 ^ (4 * inputHeight N + 1) := by
    rw [← pow_mul]
    conv_lhs => lhs; lhs; lhs; change 2 ^ 1
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  have hH : 1 ≤ inputHeight N := Nat.one_le_two_pow
  exact (labeledStateCount_le _ _ _ hbranch.1).trans
    (hproduct.trans (hidentity.le.trans
      (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by omega))))

end EditApproximation

end OAI
