import OAI.Combinatorics.ParityLifts.SparseStep

namespace OAI

namespace ParityWL.Complexity

inductive SparseTree (α : Type) where
  | leaf : ClauseList α → SparseTree α
  | branch : ClauseList α → SparseTree α → SparseTree α → SparseTree α

def SparseTree.root {α : Type} : SparseTree α → ClauseList α
  | .leaf F => F
  | .branch F _ _ => F

def SparseTree.leaves {α : Type} : SparseTree α → List (ClauseList α)
  | .leaf F => [F]
  | .branch _ l t => l.leaves++t.leaves

def SparseTree.nodes {α : Type} : SparseTree α → ℕ
  | .leaf _ => 1
  | .branch _ l t => l.nodes+t.nodes+1

lemma SparseTree.nodes_eq {α : Type} (T : SparseTree α) : T.nodes+1=2*T.leaves.length := by
  induction T with
  | leaf F => simp [nodes,leaves]
  | branch F l t hl ht => simp only [nodes,leaves,List.length_append] at *; omega

lemma SparseTree.nodes_le {α : Type} (T : SparseTree α) : T.nodes≤2*T.leaves.length := by
  have := T.nodes_eq
  omega

noncomputable def SparseTree.Valid {α : Type} [DecidableEq α] (r : ℕ) : SparseTree α → Prop
  | .leaf F => (sparseStep r F).1=true
  | .branch F l t => (sparseStep r F).1=false ∧ (sparseStep r F).2.1=l.root ∧
      (sparseStep r F).2.2=t.root ∧ l.Valid r ∧ t.Valid r

def SparseTree.All {α : Type} (P : ClauseList α → Prop) : SparseTree α → Prop
  | .leaf F => P F
  | .branch F l t => P F ∧ l.All P ∧ t.All P

lemma sparse_tree_exists {α : Type} [DecidableEq α] [Fintype α] {r : ℕ} (hr : 0<r)
    (s : Sparsification.State α (r^2)) (F : ClauseList α) (he : listCNF F=s.formula) :
    ∃ T : SparseTree α, T.root=F ∧ T.Valid r ∧
      (∀ H∈T.leaves, Sparsification.Reduced (listCNF H) ∧
        (∀ C∈listCNF H, C.card≤3) ∧ Sparsification.Terminal (listCNF H) r) ∧
      (∀ v : α → Prop, Sparsification.Holds (listCNF F) v ↔
        ∃ H∈T.leaves, Sparsification.Holds (listCNF H) v) ∧
      (T.leaves.length : ℝ)*Sparsification.branchBase r^s.spent ≤
        Sparsification.branchBase r^(3*Fintype.card α*r^2) := by
  let K := 3*Fintype.card α*r^2
  have hb : 1≤Sparsification.branchBase r := (Sparsification.branchBase_gt_one hr).le
  have hp : 0<Sparsification.branchBase r := lt_of_lt_of_le zero_lt_one hb
  suffices ∀ n : ℕ, ∀ s : Sparsification.State α (r^2), K-s.spent=n →
      ∀ F : ClauseList α, listCNF F=s.formula →
      ∃ T : SparseTree α, T.root=F ∧ T.Valid r ∧
        (∀ H∈T.leaves, Sparsification.Reduced (listCNF H) ∧
          (∀ C∈listCNF H, C.card≤3) ∧ Sparsification.Terminal (listCNF H) r) ∧
        (∀ v : α → Prop, Sparsification.Holds (listCNF F) v ↔
          ∃ H∈T.leaves, Sparsification.Holds (listCNF H) v) ∧
        (T.leaves.length : ℝ)*Sparsification.branchBase r^s.spent ≤ Sparsification.branchBase r^K by
    exact this _ s rfl F he
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s hn F he
    rcases sparseStep_spec hr s F he with ht | ⟨hflag,sp,hl,hright⟩
    · refine ⟨.leaf F,rfl,ht.1,?_,?_,?_⟩
      · intro H hH
        have hh : H=F := by simpa [SparseTree.leaves] using hH
        subst H
        rw [he]
        exact ⟨s.reduced,s.width,ht.2.2.2⟩
      · intro v; simp [SparseTree.leaves]
      · simp only [SparseTree.leaves,List.length_singleton,Nat.cast_one,one_mul]
        exact pow_le_pow_right₀ hb s.spent_bound
    · have hls := sp.left_spent
      have hrs := sp.right_spent
      have hleft : K-sp.left.spent<n := by
        have := sp.left.spent_bound
        have := sp.x_pos
        dsimp [K] at *
        omega
      have hright' : K-sp.right.spent<n := by
        have := sp.right.spent_bound
        have := sp.y_pos
        dsimp [K] at *
        omega
      obtain ⟨l,hlroot,hlvalid,hlleaf,hlholds,hlcount⟩ := ih _ hleft sp.left rfl _ hl
      obtain ⟨t,htroot,htvalid,htleaf,htholds,htcount⟩ := ih _ hright' sp.right rfl _ hright
      refine ⟨.branch F l t,rfl,⟨hflag,hlroot.symm,htroot.symm,hlvalid,htvalid⟩,?_,?_,?_⟩
      · intro H hH
        rcases List.mem_append.mp hH with hH | hH
        · exact hlleaf H hH
        · exact htleaf H hH
      · intro v
        rw [he,sp.holds,← hl,← hright,hlholds,htholds]
        simp only [SparseTree.leaves,List.mem_append,exists_or,or_and_right]
      · rw [hls] at hlcount
        rw [hrs] at htcount
        simpa only [SparseTree.leaves,List.length_append] using
          Sparsification.weighted_split (Sparsification.branchBase r) hp s.spent sp.x sp.y K
            l.leaves.length t.leaves.length hlcount htcount sp.split_bound

end ParityWL.Complexity

end OAI
