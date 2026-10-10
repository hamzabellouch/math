import OAI.Combinatorics.EditApproximation.Binary.BitQuery

namespace OAI

/-! A proof-only view of a binary-word memo as its rational-value memo.
The tree shape and every lookup/insertion path are preserved. -/

namespace EditApproximation
namespace BinaryMemo

def mapValues {α β : Type*} (f : α → β) : BinaryMemo α → BinaryMemo β
  | .empty => .empty
  | .node v l r => .node (v.map f) (mapValues f l) (mapValues f r)

@[simp] theorem mapValues_value {α β : Type*} (f : α → β) (tree : BinaryMemo α) :
    (tree.mapValues f).value = tree.value.map f := by cases tree <;> rfl

@[simp] theorem mapValues_left {α β : Type*} (f : α → β) (tree : BinaryMemo α) :
    (tree.mapValues f).left = tree.left.mapValues f := by cases tree <;> rfl

@[simp] theorem mapValues_right {α β : Type*} (f : α → β) (tree : BinaryMemo α) :
    (tree.mapValues f).right = tree.right.mapValues f := by cases tree <;> rfl

@[simp] theorem mapValues_lookup {α β : Type*} (f : α → β) (tree : BinaryMemo α) (key : List Bool) :
    (tree.mapValues f).lookup key = (tree.lookup key).map f := by
  induction key generalizing tree with
  | nil => exact mapValues_value f tree
  | cons bit rest ih => cases bit <;> simp only [lookup, mapValues_left, mapValues_right, ih]

@[simp] theorem mapValues_insert {α β : Type*} (f : α → β) (tree : BinaryMemo α)
    (key : List Bool) (value : α) :
    (tree.insert key value).mapValues f = (tree.mapValues f).insert key (f value) := by
  induction key generalizing tree with
  | nil => simp only [insert, mapValues, mapValues_left, mapValues_right, Option.map_some]
  | cons bit rest ih =>
    cases bit <;> simp only [insert, mapValues, ih, mapValues_value, mapValues_left, mapValues_right]

@[simp] theorem mapValues_nodes {α β : Type*} (f : α → β) (tree : BinaryMemo α) :
    (tree.mapValues f).nodes = tree.nodes := by
  induction tree with
  | empty => rfl
  | node v l r ihl ihr => simp only [mapValues, nodes, ihl, ihr]

end BinaryMemo
end EditApproximation

end OAI
