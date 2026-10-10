import OAI.NumberTheory.Ostmann.Tree.PreorderNodePaths

namespace OAI

namespace Ostmann

open scoped Classical

/-- The prefix of length i is an earlier internal node. -/
def ancestorNodeIndex (n : ℕ) (j : Fin (2 ^ n - 1))
    (i : Fin (preorderNodePath n j).length) : Fin (2 ^ n - 1) :=
  ⟨nodePathIndex n ((preorderNodePath n j).take i.val), nodePathIndex_lt n _ (by
    have h := preorderNodePath_length n j
    rw [List.length_take]
    exact (min_le_right _ _).trans_lt h)⟩

theorem ancestorNodeIndex_path (n : ℕ) (j : Fin (2 ^ n - 1))
    (i : Fin (preorderNodePath n j).length) :
    preorderNodePath n (ancestorNodeIndex n j i) = (preorderNodePath n j).take i.val :=
  preorderNodePath_nodePathIndex n _ (by
    rw [List.length_take]
    exact (min_le_right _ _).trans_lt (preorderNodePath_length n j))

theorem ancestorNodeIndex_earlier (n : ℕ) (j : Fin (2 ^ n - 1))
    (i : Fin (preorderNodePath n j).length) :
    (ancestorNodeIndex n j i).val < j.val ∧
      (preorderNodePath n (ancestorNodeIndex n j i)).length < (preorderNodePath n j).length := by
  have hsplit := List.take_append_drop i.val (preorderNodePath n j)
  have hdrop : (preorderNodePath n j).drop i.val ≠ [] := by
    intro hz
    have hl := congrArg List.length hz
    simp only [List.length_drop, List.length_nil] at hl
    omega
  constructor
  · change nodePathIndex n ((preorderNodePath n j).take i.val) < j.val
    rw [← nodePathIndex_preorderNodePath n j]
    conv_rhs => rw [← hsplit]
    apply nodePathIndex_proper_prefix n _ _ _ hdrop
    rw [hsplit]
    exact preorderNodePath_length n j
  · rw [ancestorNodeIndex_path, List.length_take, min_eq_left (Nat.le_of_lt i.isLt)]
    exact i.isLt

/-- The selected ancestors are genuine prefixes. Fixed label products and
which prefixes enter each coefficient may vary with the actual node. -/
noncomputable def treeAncestorScheme (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (CL CR : List Bool → ℤ)
    (AL AR : (p : List Bool) → Finset (Fin p.length)) : PivotDependencyScheme (2 ^ n - 1) where
  frequencies j := singleTreeNodeFrequencies S n t j.val
  depth j := (preorderNodePath n j).length
  fixedLeft j := CL (preorderNodePath n j)
  fixedRight j := CR (preorderNodePath n j)
  ancestorsLeft j := (AL (preorderNodePath n j)).image (ancestorNodeIndex n j)
  ancestorsRight j := (AR (preorderNodePath n j)).image (ancestorNodeIndex n j)
  earlierLeft j i hi := by
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
    exact ancestorNodeIndex_earlier n j a
  earlierRight j i hi := by
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
    exact ancestorNodeIndex_earlier n j a

theorem treeAncestorScheme_depth (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (CL CR : List Bool → ℤ) (AL AR : (p : List Bool) → Finset (Fin p.length))
    (j : Fin (2 ^ n - 1)) : (treeAncestorScheme S n t CL CR AL AR).depth j < n :=
  preorderNodePath_length n j

end Ostmann

end OAI
