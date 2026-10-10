import OAI.NumberTheory.Ostmann.Construction.ScheduledPreorderNodes
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSlotSystem
import OAI.NumberTheory.Ostmann.Construction.HistoryGiantSources

namespace OAI

/-! # Actual moving giants are the selected proper ancestor quotients

The preorder pivot array is divided by its own sampled compensation product.
The current giants use exactly these quotients, rather than the composite
pivots that enter the generic transfer-history recursion.
-/

namespace Ostmann
open scoped Classical

noncomputable def movingNodeGiant {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (node : ReconstructedTransferNode (MovingSlotState σ)) : ℕ :=
  node.pivot (movingSlotSystem value childBound pivotBound) / node.state.compensation value

noncomputable def movingGiantArray {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (n : ℕ) (x : MovingSlotState σ)
    (t : FrequencyTree ℤ n) (j : Fin (2 ^ n - 1)) : ℤ :=
  movingNodeGiant value childBound pivotBound
    (transferNodeArray (movingSlotSystem value childBound pivotBound) n x t j)

/-- Following a path updates the two giants with the actual quotient at each
proper prefix. The hypothesis just names these computed values. -/
theorem movingNodeAtPath_giants {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (n : ℕ) (T : MovingSlotData σ n)
    (t : FrequencyTree ℤ n) (XL XR : ℕ) (path : List Bool) (hp : path.length < n)
    (d : ℕ) (p : ℕ → ℤ)
    (hanc : ∀ k < path.length, p (d + k) =
      (movingNodeGiant value childBound pivotBound
        (transferNodeAtPath (movingSlotSystem value childBound pivotBound) n
          ⟨n, T, XL, XR⟩ t (path.take k)) : ℤ)) :
    let z := (transferNodeAtPath (movingSlotSystem value childBound pivotBound) n
      ⟨n, T, XL, XR⟩ t path).state
    ((z.leftGiant : ℤ), (z.rightGiant : ℤ)) =
      evolveGiantValues p d (XL, XR) path := by
  induction n generalizing XL XR path d with
  | zero => simp at hp
  | succ n ih =>
    cases T with
    | node s CL CR u left right =>
      cases path with
      | nil => rfl
      | cons b path =>
        have hp' : path.length < n := by simpa using hp
        let sys := movingSlotSystem value childBound pivotBound
        let x : MovingSlotState σ := ⟨n + 1, .node s CL CR u left right, XL, XR⟩
        let Q := historyPivot sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
        let g := Q / MovingSlotReversal.naturalProduct value u
        have hg : p d = (g : ℤ) := by
          simpa only [Nat.add_zero, List.take_zero, transferNodeAtPath,
            movingNodeGiant, ReconstructedTransferNode.pivot,
            MovingSlotState.compensation] using hanc 0 (by simp)
        cases b
        · change (((transferNodeAtPath sys n ⟨n, left, g, XL⟩ t.2.1 path).state.leftGiant : ℤ),
              ((transferNodeAtPath sys n ⟨n, left, g, XL⟩ t.2.1 path).state.rightGiant : ℤ)) = _
          rw [evolveGiantValues, hg]
          apply ih left t.2.1 g XL path hp' (d + 1)
          intro k hk
          have h := hanc (k + 1) (by simpa using Nat.add_lt_add_right hk 1)
          simpa only [Nat.add_assoc, Nat.add_comm 1 k, List.take_succ_cons,
            transferNodeAtPath, Bool.false_eq_true, ite_false, movingSlotSystem,
            MovingSlotState.child, sys, x, g, Q, ite_true] using h
        · change (((transferNodeAtPath sys n ⟨n, right, g, XR⟩ t.2.2 path).state.leftGiant : ℤ),
              ((transferNodeAtPath sys n ⟨n, right, g, XR⟩ t.2.2 path).state.rightGiant : ℤ)) = _
          rw [evolveGiantValues, hg]
          apply ih right t.2.2 g XR path hp' (d + 1)
          intro k hk
          have h := hanc (k + 1) (by simpa using Nat.add_lt_add_right hk 1)
          simpa only [Nat.add_assoc, Nat.add_comm 1 k, List.take_succ_cons,
            transferNodeAtPath, ite_true, movingSlotSystem, MovingSlotState.child,
            sys, x, g, Q, Bool.false_eq_true, ite_false] using h

/-- The source expression in the ancestor scheme evaluates to the actual
natural giant on each side of a preorder node. -/
theorem movingGiantArray_sources {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (n : ℕ) (T : MovingSlotData σ n)
    (t : FrequencyTree ℤ n) (XL XR : ℕ) (j : Fin (2 ^ n - 1)) :
    let p := movingGiantArray value childBound pivotBound n ⟨n, T, XL, XR⟩ t
    let z := (transferNodeArray (movingSlotSystem value childBound pivotBound) n
      ⟨n, T, XL, XR⟩ t j).state
    ((z.leftGiant : ℤ), (z.rightGiant : ℤ)) =
      ((historyGiantSources XL XR (preorderNodePath n j)).1.nodeValue n j p
        (historyGiantSources_known XL XR _).1,
       (historyGiantSources XL XR (preorderNodePath n j)).2.nodeValue n j p
        (historyGiantSources_known XL XR _).2) := by
  dsimp only
  rw [transferNodeArray_path]
  let p := movingGiantArray value childBound pivotBound n ⟨n, T, XL, XR⟩ t
  let q := fun k => if hk : k < (preorderNodePath n j).length then
    p (ancestorNodeIndex n j ⟨k, hk⟩) else 0
  have h := movingNodeAtPath_giants value childBound pivotBound n T t XL XR
    (preorderNodePath n j) (preorderNodePath_length n j) 0 q (by
      intro k hk
      simp only [Nat.zero_add, q, dite_eq_left hk, p, movingGiantArray,
        transferNodeArray_path, ancestorNodeIndex_path])
  have heval := evolveGiantSources_eval q 0 (.fixed (XL : ℤ), .fixed (XR : ℤ))
    (preorderNodePath n j)
  change _ = evolveGiantValues q 0 (XL, XR) (preorderNodePath n j) at heval
  rw [← heval] at h
  change _ = ((historyGiantSources XL XR (preorderNodePath n j)).1.eval q,
    (historyGiantSources XL XR (preorderNodePath n j)).2.eval q) at h
  rw [h]
  have he (s : HistoryGiantSource) (hs : s.knownBefore (preorderNodePath n j).length) :
      s.eval q = s.nodeValue n j p hs := by
    cases s with
    | fixed c => rfl
    | ancestor i =>
      change (if hi : i < (preorderNodePath n j).length then
        p (ancestorNodeIndex n j ⟨i, hi⟩) else 0) = _
      change i < (preorderNodePath n j).length at hs
      rw [dite_eq_left hs]
      rfl
  exact Prod.ext (he _ (historyGiantSources_known XL XR _).1)
    (he _ (historyGiantSources_known XL XR _).2)

end Ostmann

end OAI
