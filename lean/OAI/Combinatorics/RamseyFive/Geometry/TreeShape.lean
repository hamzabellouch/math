import Mathlib
import OAI.Combinatorics.RamseyFive.Trees.TreeOrder

namespace OAI

namespace SharpRamseyFive.TreeCodec
open BinaryTree
open scoped Classical
variable {I J : Type*}
lemma inorder_map (g : I→J) (b : BinaryTree I) :
    PivotTree.inorder (b.map g)=(PivotTree.inorder b).map g := by
  induction b with
  | nil=>rfl
  | node a l r ihl ihr=>simp only [BinaryTree.map,PivotTree.inorder,List.map_append,
      List.map_cons,ihl,ihr]

lemma address_card (b : BinaryTree I) : Fintype.card (Address b)=b.numNodes := by
  induction b with
  | nil=>rfl
  | node a l r ihl ihr=>
    have he : Fintype.card (Address (.node a l r)) = Fintype.card (Unit ⊕ (Address l ⊕ Address r)) :=
      Fintype.card_congr (Equiv.refl _)
    rw [he,Fintype.card_sum,Fintype.card_sum,Fintype.card_unit,ihl,ihr]
    simp only [BinaryTree.numNodes]
    omega
end SharpRamseyFive.TreeCodec
namespace SharpRamseyFive.PivotTree
open TreeCodec
open scoped Classical
noncomputable section

def finiteRank (n : ℕ) (j : Address (finiteBalanced n)) : Fin n :=
  ⟨(label (finiteBalanced n) j).val,finiteBalanced_label_lt n j⟩

lemma finiteRank_surjective (n : ℕ) : Function.Surjective (finiteRank n) := by
  intro i
  let a : Fin (n+1):=⟨i.val,Nat.lt_succ_of_lt i.isLt⟩
  have ha : a∈inorder (finiteBalanced n) := by
    rw [finiteBalanced,inorder_map,balanced_inorder]
    apply List.mem_map.mpr
    refine ⟨i.val,?_,?_⟩
    · rw [List.mem_range']
      exact ⟨i.val,i.isLt,by simp⟩
    · apply Fin.ext
      exact min_eq_left i.isLt.le
  obtain ⟨j,hj⟩:=exists_address_of_mem (finiteBalanced n) a ha
  refine ⟨j,?_⟩
  apply Fin.ext
  exact congrArg (fun a : Fin (n+1)=>a.val) hj

def finiteRankEquiv (n : ℕ) : Address (finiteBalanced n) ≃ Fin n :=
  Equiv.ofBijective (finiteRank n) ((Fintype.bijective_iff_surjective_and_card (finiteRank n)).mpr
    ⟨finiteRank_surjective n,by rw [address_card,finiteBalanced_nodes,Fintype.card_fin]⟩)

@[simp] lemma finiteRankEquiv_apply (n : ℕ) (j : Address (finiteBalanced n)) :
    finiteRankEquiv n j=finiteRank n j := rfl

lemma finiteRankEquiv_label (n : ℕ) (j : Fin n) :
    (label (finiteBalanced n) ((finiteRankEquiv n).symm j)).val=j.val := by
  exact congrArg Fin.val ((finiteRankEquiv n).apply_symm_apply j)
end
end SharpRamseyFive.PivotTree

end OAI
