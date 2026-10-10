import OAI.Analysis.SeparableQuotients.ExactPairs

namespace OAI

noncomputable section

namespace SeparableQuotient.BinaryNodes

def child (n : ℕ) (b : Bool) : ℕ := 2*n+1+b.toNat

def ancestors : ℕ → List ℕ
  | 0 => [0]
  | n+1 => ancestors (n/2) ++ [n+1]
termination_by n => n

def branch (b : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n+1 => child (branch b n) (b n)

lemma child_pos (n : ℕ) (b : Bool) : 0 < child n b := by simp only [child]; omega
lemma lt_child (n : ℕ) (b : Bool) : n < child n b := by simp only [child]; omega
lemma child_parent (n : ℕ) (b : Bool) : (child n b-1)/2 = n := by
  cases b <;> simp only [child,Bool.toNat_false,Bool.toNat_true] <;> omega

lemma child_injective {n m : ℕ} {b c : Bool} (h : child n b = child m c) : n = m ∧ b = c := by
  cases b <;> cases c <;> simp_all [child] <;> omega

lemma ancestors_child (n : ℕ) (b : Bool) : ancestors (child n b) = ancestors n ++ [child n b] := by
  have hpos := child_pos n b
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  rw [hk,ancestors]
  congr 2
  have hp := child_parent n b
  rw [hk] at hp
  omega

lemma ancestors_nonempty (n : ℕ) : ancestors n ≠ [] := by
  cases n with
  | zero => simp [ancestors]
  | succ n => simp [ancestors]

lemma ancestors_mem_le (n k : ℕ) (hk : k ∈ ancestors n) : k ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa [ancestors] using hk
    | succ n =>
      simp only [ancestors,List.mem_append,List.mem_singleton] at hk
      rcases hk with hk | rfl
      · exact (ih (n/2) (by omega) hk).trans (by omega)
      · exact le_rfl

lemma ancestors_branch (b : ℕ → Bool) (n : ℕ) :
    ancestors (branch b n) = List.ofFn (fun i : Fin (n+1) => branch b i) := by
  induction n with
  | zero => simp [branch,ancestors]
  | succ n ih =>
    rw [branch,ancestors_child,ih]
    rw [List.ofFn_succ_last (f := fun i : Fin (n+2) => branch b i)]
    simp only [Fin.val_castSucc,Fin.val_last]
    rfl

lemma ancestors_branch_length (b : ℕ → Bool) (n : ℕ) : (ancestors (branch b n)).length = n+1 := by
  rw [ancestors_branch,List.length_ofFn]

lemma branch_strict (b : ℕ → Bool) : StrictMono (branch b) :=
  strictMono_nat_of_lt_succ (fun _n => lt_child _ _)

lemma branch_same_level {b c : ℕ → Bool} {n m : ℕ} (h : branch b n = branch c m) : n = m := by
  have hh := congrArg (fun k => (ancestors k).length) h
  simpa only [ancestors_branch_length,Nat.add_right_cancel_iff] using hh

lemma exists_separating_node {b c : ℕ → Bool} (hbc : b ≠ c) :
    ∃ n, ∀ m, branch b n ≠ branch c m := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hbc
  refine ⟨i+1,fun m hm => ?_⟩
  have he := branch_same_level hm
  subst m
  exact hi (child_injective hm).2

end SeparableQuotient.BinaryNodes

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

lemma RawPath.code_congr_prefix {P Q : RawPath} {n : ℕ}
    (hp : ∀ i ≤ n, P.piece i = Q.piece i)
    (hw : ∀ i ≤ n, P.weight i = Q.weight i)
    (hm : ∀ i ≤ n, P.metadata i = Q.metadata i) : P.code n = Q.code n := by
  have hs : P.support n = Q.support n := by
    unfold RawPath.support
    exact Finset.biUnion_congr rfl (fun i hi => congrArg Finsupp.support (hp i (by simpa using hi)))
  have he : P.endpoint n = Q.endpoint n := by simp only [RawPath.endpoint,hs]
  have hc : P.closure n = Q.closure n := by rw [RawPath.closure,RawPath.closure,he,hm n le_rfl]
  unfold RawPath.code
  congr 1
  funext i
  rw [hp i (by omega),hw i (by omega),hm i (by omega),hc]

structure TreeNode {f : Family} (z : BlockSequence f) where
  start : ℕ
  weight : ℕ
  weight_pos : 1 ≤ weight
  pair : ExactPair z start weight
  finish : ℕ
  finish_ge : start ≤ finish
  support : pair.vector.support ⊆ z.prefixSupport finish
  metadata : ℕ
  metadata_pos : 1 ≤ metadata
  weight_le_metadata : weight ≤ metadata

namespace TreeNode
variable {f : Family} (z : BlockSequence f)

def initial : TreeNode z := by
  let e := Classical.choice (z.exists_exactPair 0 1 (by omega))
  let hb := z.support_subset_prefix 0 e.mem_tail
  exact ⟨0,1,by omega,e,hb.choose,hb.choose_spec.1,hb.choose_spec.2,1,by omega,by omega⟩

def lookup (l : List (TreeNode z)) (n : ℕ) : TreeNode z := l.getD n (initial z)

def rawAlong (D : ℕ → TreeNode z) (v : ℕ → ℕ) : RawPath where
  piece := fun n => (D (v n)).pair.piece.value
  weight := fun n => (D (v n)).weight
  metadata := fun n => (D (v n)).metadata
  nonzero := fun n => (D (v n)).pair.piece.value_ne_zero

def nodeCode (D : ℕ → TreeNode z) (n : ℕ) : Code :=
  (rawAlong z D (fun i => (BinaryNodes.ancestors n).getD i 0)).code
    ((BinaryNodes.ancestors n).length-1)

def requested (l : List (TreeNode z)) : ℕ :=
  if l.length = 0 then 1 else sigma (nodeCode z (lookup z l) ((l.length-1)/2))

lemma requested_pos (l : List (TreeNode z)) : 1 ≤ requested z l := by
  unfold requested
  split_ifs
  · omega
  · have := codeBound_lt_sigma (nodeCode z (lookup z l) ((l.length-1)/2))
    omega

def listSupport (l : List (TreeNode z)) : Finset Γ :=
  l.toFinset.biUnion (fun d => d.pair.piece.value.support)

lemma mem_listSupport (l : List (TreeNode z)) (α : Γ) :
    α ∈ listSupport z l ↔ ∃ d ∈ l, α ∈ d.pair.piece.value.support := by
  simp [listSupport]

def nextStart (l : List (TreeNode z)) : ℕ := l.toFinset.sup (fun d => d.finish)

def next (l : List (TreeNode z)) : TreeNode z := by
  let e := Classical.choice (z.exists_exactPair (nextStart z l) (requested z l) (requested_pos z l))
  let hb := z.support_subset_prefix _ e.mem_tail
  let S := listSupport z l ∪ e.piece.value.support
  let R := S.sup (fun α => S.sup (fun β => rho α β))
  let p := 1 + requested z l + l.toFinset.sup (fun d => d.metadata) + R
  exact ⟨nextStart z l,requested z l,requested_pos z l,e,hb.choose,hb.choose_spec.1,hb.choose_spec.2,p,by dsimp [p]; omega,
    by dsimp [p]; omega⟩

lemma next_start (l : List (TreeNode z)) : (next z l).start = nextStart z l := rfl
lemma next_weight (l : List (TreeNode z)) : (next z l).weight = requested z l := rfl

lemma next_metadata_gt (l : List (TreeNode z)) (d : TreeNode z) (hd : d ∈ l) :
    d.metadata < (next z l).metadata := by
  have h := Finset.le_sup (f := fun d : TreeNode z => d.metadata) (List.mem_toFinset.mpr hd)
  change _ < 1 + requested z l + l.toFinset.sup (fun d => d.metadata) + _
  omega

lemma next_rho (l : List (TreeNode z)) (α β : Γ)
    (hα : α ∈ listSupport z l ∪ (next z l).pair.piece.value.support)
    (hβ : β ∈ listSupport z l ∪ (next z l).pair.piece.value.support) :
    rho α β ≤ (next z l).metadata := by
  let S := listSupport z l ∪ (next z l).pair.piece.value.support
  have h : rho α β ≤ S.sup (fun x => S.sup (fun y => rho x y)) :=
    (Finset.le_sup (s := S) (f := fun y => rho α y) hβ).trans
      (Finset.le_sup (s := S) (f := fun x => S.sup (fun y => rho x y)) hα)
  change _ ≤ 1 + requested z l + l.toFinset.sup (fun d => d.metadata) + S.sup (fun x => S.sup (fun y => rho x y))
  omega

def state : ℕ → List (TreeNode z)
  | 0 => []
  | n+1 => state n ++ [next z (state n)]

def node (n : ℕ) : TreeNode z := next z (state z n)

lemma state_eq_ofFn (n : ℕ) : state z n = List.ofFn (fun i : Fin n => node z i) := by
  induction n with
  | zero => simp [state]
  | succ n ih =>
    rw [state,List.ofFn_succ_last (f := fun i : Fin (n+1) => node z i)]
    change state z n ++ [node z n] = _
    rw [ih]
    rfl

lemma state_length (n : ℕ) : (state z n).length = n := by rw [state_eq_ofFn,List.length_ofFn]

lemma lookup_state {n k : ℕ} (hk : k < n) : lookup z (state z n) k = node z k := by
  simp [lookup,state_eq_ofFn,List.getD,hk]

lemma mem_state {n k : ℕ} (hk : k < n) : node z k ∈ state z n := by
  rw [state_eq_ofFn]
  exact List.mem_ofFn.mpr ⟨⟨k,hk⟩,rfl⟩

lemma finish_le_start {n k : ℕ} (hk : k < n) : (node z k).finish ≤ (node z n).start := by
  change _ ≤ (next z (state z n)).start
  rw [next_start]
  exact Finset.le_sup (List.mem_toFinset.mpr (mem_state z hk))

lemma metadata_strict : StrictMono (fun n => (node z n).metadata) := by
  intro n k hnk
  exact next_metadata_gt z (state z k) (node z n) (mem_state z hnk)

lemma support_before {n k : ℕ} (hk : k ≤ n) {α : Γ}
    (hα : α ∈ (node z k).pair.piece.value.support) :
    α ∈ listSupport z (state z n) ∪ (node z n).pair.piece.value.support := by
  rcases eq_or_lt_of_le hk with rfl | hk
  · exact Finset.mem_union_right _ hα
  · exact Finset.mem_union_left _ ((mem_listSupport z _ _).mpr ⟨node z k,mem_state z hk,hα⟩)

lemma successive_vector {n k : ℕ} (hk : k < n) :
    ∀ α ∈ (node z k).pair.vector.support, ∀ β ∈ (node z n).pair.vector.support,
      α < β ∧ (f = .mixed → Colors.color α < Colors.color β) :=
  z.prefix_tail_successive _ (node z k).support
    (z.tailSpan_mono (finish_le_start z hk) (node z n).pair.mem_tail)

lemma successive_piece {n k : ℕ} (hk : k < n) :
    Successive f (node z k).pair.piece.value (node z n).pair.piece.value := by
  intro α hα β hβ
  exact vectorCrop_successive _ _ (successive_vector z hk)
    α ((node z k).pair.support α hα) β ((node z n).pair.support β hβ)

lemma nodeCode_eq_branch (b : ℕ → Bool) (n : ℕ) :
    nodeCode z (node z) (BinaryNodes.branch b n) =
      (rawAlong z (node z) (BinaryNodes.branch b)).code n := by
  unfold nodeCode
  rw [BinaryNodes.ancestors_branch,List.length_ofFn]
  simp only [Nat.add_sub_cancel]
  apply RawPath.code_congr_prefix
  all_goals
    intro i hi
    have hlen : i < (List.ofFn (fun j : Fin (n+1) => BinaryNodes.branch b j)).length := by
      rw [List.length_ofFn]; omega
    have he : (List.ofFn (fun j : Fin (n+1) => BinaryNodes.branch b j)).getD i 0 = BinaryNodes.branch b i := by
      rw [List.getD_eq_getElem _ _ hlen,List.getElem_ofFn]
    simp only [rawAlong]
    rw [he]

lemma nodeCode_lookup {n k : ℕ} (hk : k < n) :
    nodeCode z (lookup z (state z n)) k = nodeCode z (node z) k := by
  unfold nodeCode
  apply RawPath.code_congr_prefix
  all_goals
    intro i hi
    have hi' : i < (BinaryNodes.ancestors k).length := by
      have := List.length_pos_iff.mpr (BinaryNodes.ancestors_nonempty k)
      omega
    have hm : (BinaryNodes.ancestors k).getD i 0 ∈ BinaryNodes.ancestors k := by
      simpa only [List.getD_eq_getElem _ _ hi'] using List.getElem_mem hi'
    have hle := BinaryNodes.ancestors_mem_le k _ hm
    have he := lookup_state z (n := n) (k := (BinaryNodes.ancestors k).getD i 0) (hle.trans_lt hk)
    simp only [rawAlong]
    rw [he]

lemma weight_rule (b : ℕ → Bool) (n : ℕ) :
    (node z (BinaryNodes.branch b (n+1))).weight =
      sigma ((rawAlong z (node z) (BinaryNodes.branch b)).code n) := by
  let k := BinaryNodes.branch b (n+1)
  have hk : 0 < k := BinaryNodes.child_pos _ _
  have hp : (k-1)/2 = BinaryNodes.branch b n := BinaryNodes.child_parent _ _
  change (next z (state z k)).weight = _
  rw [next_weight,requested,state_length,ite_eq_right (Nat.ne_of_gt hk),hp]
  have hpk : BinaryNodes.branch b n < k := BinaryNodes.lt_child _ _
  rw [nodeCode_lookup z hpk,nodeCode_eq_branch]

/-- The prescribed-weight exact-pair construction yields actual admissible
paths on all infinite binary branches; records include all original metadata. -/
def branchPath (b : ℕ → Bool) : InfinitePath f where
  raw := rawAlong z (node z) (BinaryNodes.branch b)
  admissible := {
    successive := fun i j hij α hα β hβ => (successive_piece z (BinaryNodes.branch_strict b hij) α hα β hβ).1
    metadata_strict := (metadata_strict z).comp (BinaryNodes.branch_strict b)
    metadata_pos := fun i => (node z (BinaryNodes.branch b i)).metadata_pos
    weight_pos := fun i => (node z (BinaryNodes.branch b i)).weight_pos
    weight_le_metadata := fun i => (node z (BinaryNodes.branch b i)).weight_le_metadata
    rho_bound := by
      intro n α β hα hβ _hab
      apply next_rho z (state z (BinaryNodes.branch b n))
      · obtain ⟨i,hi,hiα⟩ := (RawPath.mem_support_iff _ n α).mp hα
        exact support_before z ((BinaryNodes.branch_strict b).monotone hi) hiα
      · obtain ⟨i,hi,hiβ⟩ := (RawPath.mem_support_iff _ n β).mp hβ
        exact support_before z ((BinaryNodes.branch_strict b).monotone hi) hiβ
    rule := weight_rule z b }
  piece := fun i => (node z (BinaryNodes.branch b i)).pair.piece
  value_eq := fun _ => rfl
  weight_eq := fun i => (node z (BinaryNodes.branch b i)).pair.weight_eq
  successive := fun _i _j hij => successive_piece z (BinaryNodes.branch_strict b hij)
  children_mem := fun i j => (node z (BinaryNodes.branch b i)).pair.child_mem j

end TreeNode
end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology
namespace TreeNode
variable {f : Family} (z : BlockSequence f)

lemma cross_evaluate {i j : ℕ} (hij : i ≠ j) :
    norming.evaluateArray (norming.includeFinite (node z j).pair.vector) (node z i).pair.piece.value = 0 := by
  apply evaluateArray_finite_disjoint
  apply Finset.disjoint_left.mpr
  intro α hα hβ
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact (lt_irrefl α) (vectorCrop_successive (node z i).pair.nonzero (node z j).pair.nonzero
      (successive_vector z hij) α ((node z i).pair.support α hβ)
      α (support_mem_vectorCrop f _ _ α hα)).1
  · exact (lt_irrefl α) (vectorCrop_successive (node z j).pair.nonzero (node z i).pair.nonzero
      (successive_vector z hji) α (support_mem_vectorCrop f _ _ α hα)
      α ((node z i).pair.support α hβ)).1

lemma pathPartial_node (b : ℕ → Bool) (n N : ℕ) (hn : n ≤ N) :
    pathPartial (branchPath z b) N (norming.includeFinite (node z (BinaryNodes.branch b n)).pair.vector) =
      norming.evaluateArray (norming.includeFinite (node z (BinaryNodes.branch b n)).pair.vector)
        (node z (BinaryNodes.branch b n)).pair.piece.value := by
  rw [pathPartial, ← norming.evaluateArray_eq_functional]
  change norming.evaluateArray _ (∑ j : Fin (N+1), (node z (BinaryNodes.branch b j)).pair.piece.value) = _
  rw [map_sum]
  apply Finset.sum_eq_single (⟨n,by omega⟩ : Fin (N+1))
  · intro j _ hj
    exact cross_evaluate z (fun he => hj (Fin.ext ((BinaryNodes.branch_strict b).injective he)))
  · simp

lemma pathPartial_other (b : ℕ → Bool) (k : ℕ) (hk : ∀ j, BinaryNodes.branch b j ≠ k) (N : ℕ) :
    pathPartial (branchPath z b) N (norming.includeFinite (node z k).pair.vector) = 0 := by
  rw [pathPartial, ← norming.evaluateArray_eq_functional]
  change norming.evaluateArray _ (∑ j : Fin (N+1), (node z (BinaryNodes.branch b j)).pair.piece.value) = 0
  rw [map_sum]
  exact Finset.sum_eq_zero (fun j _ => cross_evaluate z (hk j))

lemma pathFunctional_node (b : ℕ → Bool) (n : ℕ) :
    1/2 ≤ pathFunctional (branchPath z b) (norming.includeFinite (node z (BinaryNodes.branch b n)).pair.vector) := by
  let x := norming.includeFinite (node z (BinaryNodes.branch b n)).pair.vector
  have he : pathFunctional (branchPath z b) x = norming.evaluateArray x
      (node z (BinaryNodes.branch b n)).pair.piece.value :=
    tendsto_nhds_unique (pathPartial_tendsto (branchPath z b) x)
      (tendsto_const_nhds.congr' ((eventually_ge_atTop n).mono (fun N hN => (pathPartial_node z b n N hN).symm)))
  rw [he]
  exact (node z (BinaryNodes.branch b n)).pair.eval_ge

lemma pathFunctional_other (b : ℕ → Bool) (k : ℕ) (hk : ∀ j, BinaryNodes.branch b j ≠ k) :
    pathFunctional (branchPath z b) (norming.includeFinite (node z k).pair.vector) = 0 :=
  tendsto_nhds_unique (pathPartial_tendsto (branchPath z b) _)
    (tendsto_const_nhds.congr' (Eventually.of_forall (fun N => (pathPartial_other z b k hk N).symm)))

lemma pair_mem_submodule (V : Submodule ℝ E) (hV : ∀ n, z.embed n ∈ V) (k : ℕ) :
    norming.includeFinite (node z k).pair.vector ∈ V := by
  have hspan : z.tailSpan (node z k).start ≤ V.comap norming.includeFinite := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n,rfl⟩
    exact hV (n+(node z k).start)
  exact hspan (node z k).pair.mem_tail

/-- Path restrictions are uniformly separated on every subspace containing the block sequence, with separation constant 1/500. -/
lemma restricted_separated (V : Submodule ℝ E) (hV : ∀ n, z.embed n ∈ V)
    {b c : ℕ → Bool} (hbc : b ≠ c) :
    (1/1000 : ℝ) ≤ ‖(pathFunctional (branchPath z b)).comp V.subtypeL -
      (pathFunctional (branchPath z c)).comp V.subtypeL‖ := by
  obtain ⟨n,hn⟩ := BinaryNodes.exists_separating_node hbc
  let x := norming.includeFinite (node z (BinaryNodes.branch b n)).pair.vector
  let v : V := ⟨x,pair_mem_submodule z V hV _⟩
  let T := (pathFunctional (branchPath z b)).comp V.subtypeL -
    (pathFunctional (branchPath z c)).comp V.subtypeL
  have hv : ‖v‖ ≤ 500 := (node z (BinaryNodes.branch b n)).pair.norm_le
  have he : 1/2 ≤ T v := by
    change 1/2 ≤ pathFunctional (branchPath z b) x - pathFunctional (branchPath z c) x
    rw [pathFunctional_other z c _ (fun j => (hn j).symm),sub_zero]
    exact pathFunctional_node z b n
  have hb := (T.le_opNorm v).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg T))
  rw [Real.norm_eq_abs] at hb
  have hp := le_abs_self (T v)
  change 1/1000 ≤ ‖T‖
  linarith

end TreeNode
end SeparableQuotient.ActualSpace

end

end OAI
