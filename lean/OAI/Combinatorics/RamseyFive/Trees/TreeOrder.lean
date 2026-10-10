import Mathlib
import OAI.Combinatorics.RamseyFive.Trees.TreeExposure

namespace OAI

namespace SharpRamseyFive.TreeCodec
open BinaryTree
open scoped Classical BigOperators
variable {I J : Type*} [Preorder I] [Preorder J]

def Ordered : BinaryTree I→Prop
  | .nil=>True
  | .node a l r=>(∀ j:Address l,label l j≤a) ∧
      (∀ j:Address r,a≤label r j) ∧ Ordered l ∧ Ordered r

omit [Preorder I] in
lemma label_mem_inorder (b : BinaryTree I) (j : Address b) : label b j∈PivotTree.inorder b := by
  induction b with
  | nil=>exact nomatch j
  | node a l r ihl ihr=>
    rcases j with j | (j | j)
    · simp [label,PivotTree.inorder]
    · exact List.mem_append_left _ (ihl j)
    · exact List.mem_append_right _ (List.mem_cons_of_mem a (ihr j))

omit [Preorder I] in
lemma exists_address_of_mem (b : BinaryTree I) (a : I) (ha : a∈PivotTree.inorder b) :
    ∃ j:Address b,label b j=a := by
  induction b with
  | nil=>simp [PivotTree.inorder] at ha
  | node v l r ihl ihr=>
    rcases List.mem_append.mp ha with h | h
    · obtain ⟨j,hj⟩:=ihl h
      exact ⟨.inr (.inl j),hj⟩
    · rcases List.mem_cons.mp h with h | h
      · exact ⟨.inl (),h.symm⟩
      · obtain ⟨j,hj⟩:=ihr h
        exact ⟨.inr (.inr j),hj⟩

lemma ordered_pathBudget_bound (b : BinaryTree I) (hb : Ordered b) (j : Address b)
    (f g : I→ℝ) (ε : ℝ) (hε : 0≤ε)
    (hf : ∀ a,label b j≤a→f a≤ε) (hg : ∀ a,a≤label b j → g a≤ε) :
    pathBudget f g b j≤b.height*ε := by
  induction b with
  | nil=>exact nomatch j
  | node a l r ihl ihr=>
    obtain ⟨hleft,hright,hl,hr⟩:=hb
    have hL : (l.height:ℝ)+1≤(BinaryTree.node a l r).height := by
      simp only [BinaryTree.height,Nat.cast_add,Nat.cast_one]
      exact_mod_cast Nat.add_le_add_right (le_max_left _ _) 1
    have hR : (r.height:ℝ)+1≤(BinaryTree.node a l r).height := by
      simp only [BinaryTree.height,Nat.cast_add,Nat.cast_one]
      exact_mod_cast Nat.add_le_add_right (le_max_right _ _) 1
    rcases j with j | (j | j)
    · exact mul_nonneg (Nat.cast_nonneg _) hε
    · have h1:=ihl hl j hf hg
      have h2:=hf a (hleft j)
      have h3:=mul_le_mul_of_nonneg_right hL hε
      change f a+pathBudget f g l j≤_
      linarith
    · have h1:=ihr hr j hf hg
      have h2:=hg a (hright j)
      have h3:=mul_le_mul_of_nonneg_right hR hε
      change g a+pathBudget f g r j≤_
      linarith

omit [Preorder I] [Preorder J] in
lemma label_map_mem (g : I→J) (b : BinaryTree I) (j : Address (b.map g)) :
    ∃ k:Address b,label (b.map g) j=g (label b k) := by
  induction b with
  | nil=>exact nomatch j
  | node a l r ihl ihr=>
    rcases j with j | (j | j)
    · exact ⟨.inl (),rfl⟩
    · obtain ⟨k,hk⟩:=ihl j
      exact ⟨.inr (.inl k),hk⟩
    · obtain ⟨k,hk⟩:=ihr j
      exact ⟨.inr (.inr k),hk⟩

lemma ordered_map (g : I→J) (hg : Monotone g) (b : BinaryTree I) (hb : Ordered b) :
    Ordered (b.map g) := by
  induction b with
  | nil=>trivial
  | node a l r ihl ihr=>
    refine ⟨?_,?_,ihl hb.2.2.1,ihr hb.2.2.2⟩
    · intro j
      obtain ⟨k,hk⟩:=label_map_mem g l j
      rw [hk]
      exact hg (hb.1 k)
    · intro j
      obtain ⟨k,hk⟩:=label_map_mem g r j
      rw [hk]
      exact hg (hb.2.1 k)

omit [Preorder I] [Preorder J] in
lemma map_height (g : I→J) (b : BinaryTree I) : (b.map g).height=b.height := by
  induction b with
  | nil=>rfl
  | node a l r ihl ihr=>simp only [BinaryTree.map,BinaryTree.height,ihl,ihr]

omit [Preorder I] [Preorder J] in
lemma map_nodes (g : I→J) (b : BinaryTree I) : (b.map g).numNodes=b.numNodes := by
  induction b with
  | nil=>rfl
  | node a l r ihl ihr=>simp only [BinaryTree.map,BinaryTree.numNodes,ihl,ihr]
end SharpRamseyFive.TreeCodec

namespace SharpRamseyFive.PivotTree
open BinaryTree TreeCodec
lemma balanced_label_bounds (lo n : ℕ) (j : Address (balanced lo n)) :
    lo≤label (balanced lo n) j ∧ label (balanced lo n) j<lo+n := by
  have h:=label_mem_inorder (balanced lo n) j
  rw [balanced_inorder,List.mem_range'] at h
  obtain ⟨i,hi,he⟩:=h
  constructor <;> omega

lemma balanced_ordered (lo n : ℕ) : Ordered (balanced lo n) := by
  induction n using Nat.strong_induction_on generalizing lo with
  | h n ih=>
    cases n with
    | zero=>simp [balanced,Ordered]
    | succ n=>
      rw [balanced,Ordered]
      refine ⟨?_,?_,ih _ (by omega) _,ih _ (by omega) _⟩
      · intro j
        have h:=(balanced_label_bounds lo (n/2) j).2
        omega
      · intro j
        have h:=(balanced_label_bounds (lo+n/2+1) (n-n/2) j).1
        omega

def finiteBalanced (n : ℕ) : BinaryTree (Fin (n+1)) :=
  (balanced 0 n).map (fun i=>⟨min i n,Nat.lt_succ_of_le (min_le_right _ _)⟩)

lemma finiteBalanced_ordered (n : ℕ) : Ordered (finiteBalanced n) := by
  apply ordered_map _ _ _ (balanced_ordered _ _)
  intro i j h
  exact min_le_min_right _ h

lemma finiteBalanced_height (H n : ℕ) (hn : n<2^H) : (finiteBalanced n).height≤H := by
  rw [finiteBalanced,map_height]
  exact balanced_height H 0 n hn

lemma finiteBalanced_nodes (n : ℕ) : (finiteBalanced n).numNodes=n := by
  rw [finiteBalanced,map_nodes,balanced_nodes]

lemma finiteBalanced_label_lt (n : ℕ) (j : Address (finiteBalanced n)) :
    (label (finiteBalanced n) j).val<n := by
  obtain ⟨k,hk⟩:=label_map_mem (fun i=>⟨min i n,Nat.lt_succ_of_le (min_le_right _ _)⟩ : ℕ→Fin (n+1))
    (balanced 0 n) j
  change (label ((balanced 0 n).map _) j).val<n
  rw [hk]
  have h:=(balanced_label_bounds 0 n k).2
  change min _ n<n
  omega
end SharpRamseyFive.PivotTree

end OAI
