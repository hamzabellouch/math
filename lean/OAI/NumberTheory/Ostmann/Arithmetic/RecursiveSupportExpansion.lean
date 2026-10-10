import OAI.NumberTheory.Ostmann.Arithmetic.RecursiveNodeExpansion

namespace OAI

/-! # All original range factors and all arithmetic tests in a flat history -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def transferNodeCutoff {State : Type*}
    (cutoff : State → ℤ → ℤ → ℤ → ℝ) (node : ReconstructedTransferNode State) : ℝ :=
  cutoff node.state node.root node.left node.right

noncomputable def transferLeafCutoff {State : Type*}
    (cutoff : State → ℤ → ℝ) (leaf : (State × ℤ) × Bool) : ℝ :=
  cutoff leaf.1.1 leaf.1.2

theorem transferLeafCutoff_flip {State : Type*} (c : State → ℤ → ℝ)
    (l : List ((State × ℤ) × Bool)) :
    ((l.map (fun z => (z.1, !z.2))).map (transferLeafCutoff c)).prod =
      (l.map (transferLeafCutoff c)).prod := by
  simp only [List.map_map, Function.comp_def, transferLeafCutoff]
  rfl

/-- The support is exactly the product of original node and leaf cutoffs
on the original arithmetic validity set. -/
theorem recursiveSupportFactor_product {State : Type*}
    (sys : TransferHistorySystem State) (leafCutoff : State → ℤ → ℝ)
    (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) :
    recursiveSupportFactor sys leafCutoff cutoff n σ t =
      if ValidTransferHistory sys n σ t then
        ((transferNodeList sys n σ t).map (transferNodeCutoff cutoff)).prod *
          ((transferLeafList sys n σ t).map (transferLeafCutoff leafCutoff)).prod
      else 0 := by
  induction n generalizing σ with
  | zero => simp [recursiveSupportFactor, ValidTransferHistory, transferNodeList,
      transferLeafList, transferLeafCutoff]
  | succ n ih =>
    rw [validTransferHistory_reconstructed_iff]
    simp only [recursiveSupportFactor, transferNodeList, transferLeafList,
      List.map_cons, List.prod_cons, List.map_append, List.prod_append,
      transferLeafCutoff_flip, transferNodeCutoff, ReconstructedTransferNode.pivot, ih]
    split_ifs <;> simp_all
    ring

/-- The flat statement uses exactly 2^n-1 node tests, whose validity was
proved equivalent to the recursive support, not assumed as a new condition. -/
theorem recursiveSupportFactor_nodeList {State : Type*}
    (sys : TransferHistorySystem State) (leafCutoff : State → ℤ → ℝ)
    (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) :
    recursiveSupportFactor sys leafCutoff cutoff n σ t =
      if ∀ node ∈ transferNodeList sys n σ t, node.Valid sys then
        ((transferNodeList sys n σ t).map (transferNodeCutoff cutoff)).prod *
          ((transferLeafList sys n σ t).map (transferLeafCutoff leafCutoff)).prod
      else 0 := by
  rw [recursiveSupportFactor_product, validTransferHistory_nodeList_iff]
  congr 1

end Ostmann

end OAI
