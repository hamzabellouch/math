import Mathlib
import OAI.Algebra.GroupRing.MapEuler

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TreeCentroid
open scoped Classical
open SimpleGraph
variable {V : Type} [Fintype V] {G : SimpleGraph V} (h : G.IsTree)

omit [Fintype V] in
lemma next_of_adj {c n : V} (he : G.Adj c n) : next h c n=n := by
  exact (h.isAcyclic.eq_snd_of_adj_start (path_isPath h c n) he (path h c n).end_mem_support).symm

lemma branch_head {c n : V} (he : G.Adj c n) : n∈branch h c n :=
  (mem_branch h).mpr ⟨he.ne',next_of_adj h he⟩

/-- A tree branch has exactly one possible directed edge leaving it. -/
lemma branch_boundary {c n x y : V} (hx : x∈branch h c n) (hy : y∉branch h c n)
    (he : G.Adj x y) : x=n ∧ y=c := by
  have hyc : y=c := by
    by_contra hn
    exact hy (branch_closed h hx hn he)
  subst y
  have hn := (mem_branch h).mp hx
  have heq := next_of_adj h he.symm
  exact ⟨heq.symm.trans hn.2,rfl⟩

lemma branch_walk_boundary {c n x y : V} (hx : x∉branch h c n) (hy : y∈branch h c n)
    (p : G.Walk x y) : n∈p.support := by
  induction p with
  | nil => exact (hx hy).elim
  | @cons x z y e p ih =>
    by_cases hz : z∈branch h c n
    · have he := branch_boundary h hz hx e.symm
      simp only [Walk.support_cons,List.mem_cons]
      exact Or.inr (he.1 ▸ p.start_mem_support)
    · simp only [Walk.support_cons,List.mem_cons]
      exact Or.inr (ih hz hy)

/-- Descendants are defined by the actual branch beyond the parent edge. -/
def descendants (root v : V) : Finset V := branch h (next h v root) v

lemma root_not_descendants {root v : V} (hv : v≠root) : root∉descendants h root v := by
  intro hr
  obtain ⟨hr,hn⟩ := (mem_branch h).mp hr
  have hd := dist_next h hv
  have hd' := dist_next h hr.symm
  rw [hn] at hd'
  omega

lemma self_mem_descendants {root v : V} (hv : v≠root) : v∈descendants h root v :=
  branch_head h (next_adj h hv).symm

lemma descendant_mem_root_path {root v w : V} (hv : v≠root) (hw : w∈descendants h root v) :
    v∈(path h root w).support :=
  branch_walk_boundary h (root_not_descendants h hv) hw (path h root w)

def rootPath (root v : V) : Finset V := (path h root v).support.toFinset
omit [Fintype V] in
lemma root_mem_rootPath (root v : V) : root∈rootPath h root v :=
  List.mem_toFinset.mpr (path h root v).start_mem_support
omit [Fintype V] in
lemma self_mem_rootPath (root v : V) : v∈rootPath h root v :=
  List.mem_toFinset.mpr (path h root v).end_mem_support
omit [Fintype V] in
lemma rootPath_card (root v : V) : (rootPath h root v).card=G.dist root v+1 := by
  rw [rootPath,List.toFinset_card_of_nodup (path_isPath h root v).support_nodup,
    Walk.length_support,path_length]

omit [Fintype V] in
/-- Two root paths share the root, yielding the sharp 2r+1 count rather than
an erroneous 2r+2 or a three-path 3r+1 bound. -/
theorem two_root_paths_card (root v w : V) (r : ℕ)
    (hv : G.dist root v≤r) (hw : G.dist root w≤r) :
    (rootPath h root v∪rootPath h root w).card≤2*r+1 := by
  have he := Finset.card_union_add_card_inter (rootPath h root v) (rootPath h root w)
  have hp : 0<(rootPath h root v∩rootPath h root w).card :=
    Finset.card_pos.mpr ⟨root,Finset.mem_inter.mpr ⟨root_mem_rootPath h _ _,root_mem_rootPath h _ _⟩⟩
  rw [rootPath_card,rootPath_card] at he
  omega

end TorsionFreeZeroDivisors.TreeCentroid

namespace TorsionFreeZeroDivisors.MapEuler

section
open scoped Classical
open PermutationCycles
variable {O : Type} (σ φ γ : Equiv.Perm O) (hγ : Function.Involutive γ)

/-- Dual edges incident to a specified set of primal vertices. -/
def touchGraph (S : Set (Cycle σ)) : SimpleGraph (Cycle φ) where
  Adj f g := f≠g ∧ ∃ x,cycle φ x=f ∧ cycle φ (γ x)=g ∧
    (cycle σ x∈S ∨ cycle σ (γ x)∈S)
  symm := ⟨by
    rintro f g ⟨hne,x,hx,hy,hS⟩
    refine ⟨hne.symm,γ x,hy,?_,?_⟩
    · rwa [hγ]
    · rw [hγ]
      exact hS.symm⟩
  loopless := ⟨fun _ h=>h.1 rfl⟩

lemma touchGraph_le (S : Set (Cycle σ)) : touchGraph σ φ γ hγ S≤graph φ γ hγ := by
  rintro f g ⟨hne,x,hx,hy,_⟩
  exact ⟨hne,x,hx,hy⟩

lemma touchGraph_contour_step (θ : Equiv.Perm O) (hθ : γ*θ=φ)
    (S : Set (Cycle σ)) (x : O) (hx : cycle σ (θ x)∈S) :
    (touchGraph σ φ γ hγ S).Reachable (cycle φ x) (cycle φ (θ x)) := by
  by_cases he : cycle φ x=cycle φ (θ x)
  · rw [he]
  · have hp : γ (θ x)=φ x := congrArg (fun f : Equiv.Perm O=>f x) hθ
    apply SimpleGraph.Reachable.symm
    apply SimpleGraph.Adj.reachable
    exact ⟨Ne.symm he,θ x,rfl,by rw [hp,cycle_apply],Or.inl hx⟩

variable [Fintype O]
/-- A subtree interval in the primal contour gives actual connectivity through
only those dual edges incident to the subtree. -/
theorem touchGraph_connected_of_contour (θ : Equiv.Perm O) (hθ : γ*θ=φ)
    (hc : Nat.card (Cycle θ)=1) (S : Set (Cycle σ)) (p : O)
    (hout : ∀ x,cycle σ x∈S → cycle σ (θ x)∉S → x=p)
    {x y : O} (hx : cycle σ x∈S) (hy : cycle σ y∈S) :
    (touchGraph σ φ γ hγ S).Reachable (cycle φ x) (cycle φ y) := by
  have hh (z : O) (hz : cycle σ z∈S) := contour_interval_reachable θ
    (sameCycle_of_card_one θ hc) {x | cycle σ x∈S} p hout
    (touchGraph σ φ γ hγ S) (cycle φ)
    (fun x _ h=>touchGraph_contour_step σ φ γ hγ θ hθ S x h) z hz
  exact (hh x hx).symm.trans (hh y hy)

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (ha : Function.Involutive α)
    (T : SimpleGraph (Cycle σ)) (hT : T≤graph σ α ha) (ht : T.IsTree)

/-- Every rooted tree branch has a unique possible exit in the actual contour. -/
theorem branch_contour_exit {c n : Cycle σ} (he : T.Adj n c) :
    ∃ p : O,∀ x,cycle σ x∈TreeCentroid.branch ht c n →
      cycle σ ((subgraphPair σ α ha T hT*σ) x)∉TreeCentroid.branch ht c n → x=p := by
  have he' : (graph σ (subgraphPair σ α ha T hT)
      (subgraphPair_involutive σ α ha T hT)).Adj n c := by
    rwa [subgraphPair_graph]
  obtain ⟨hne,p,hp,hq⟩ := he'
  have hpn : subgraphPair σ α ha T hT p≠p := fun h=>hne (hp.symm.trans (h ▸ hq))
  refine ⟨σ.symm p,fun x hx hy=>?_⟩
  have hx' : cycle σ (σ x)∈TreeCentroid.branch ht c n := by rwa [cycle_apply]
  have hxn : subgraphPair σ α ha T hT (σ x)≠σ x := by
    intro h
    exact hy (h.symm ▸ hx')
  have hb := TreeCentroid.branch_boundary ht hx' hy
    (subgraphPair_adj σ α ha T hT hxn)
  have heq := subgraphPair_dart_unique σ α ha T hT hxn hpn
    (hb.1.trans hp.symm) (hb.2.trans hq.symm)
  exact σ.injective (heq.trans (σ.apply_symm_apply p).symm)

/-- Literal face connectivity around a primal tree branch in a genus-zero
map, using only cotree edges touching that branch. -/
theorem branch_dual_touch_connected (hz : GenusZero σ α) {c n : Cycle σ}
    (he : T.Adj n c) {x y : O}
    (hx : cycle σ x∈TreeCentroid.branch ht c n)
    (hy : cycle σ y∈TreeCentroid.branch ht c n) :
    (touchGraph σ (α*σ) (α*subgraphPair σ α ha T hT)
      (complement_involutive α _ ha (subgraphPair_involutive σ α ha T hT)
        (subgraphPair_subpairing σ α ha T hT))
      (↑(TreeCentroid.branch ht c n) : Set (Cycle σ))).Reachable
      (cycle (α*σ) x) (cycle (α*σ) y) := by
  obtain ⟨p,hp⟩ := branch_contour_exit σ α ha T hT ht he
  apply touchGraph_connected_of_contour σ (α*σ) (α*subgraphPair σ α ha T hT) _
    (subgraphPair σ α ha T hT*σ) _ (tree_contour_card σ α ha T hT hz ht) _ p hp hx hy
  ext z
  change α (subgraphPair σ α ha T hT (subgraphPair σ α ha T hT (σ z)))=α (σ z)
  rw [subgraphPair_involutive σ α ha T hT]

end

open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (ha : Function.Involutive α)

def supportedRealize (d : (graph σ α ha).Dart) : {x // x∈α.support} :=
  ⟨realizeDart σ α ha d,realizeDart_mem σ α ha d⟩
lemma supportedRealize_injective : Function.Injective (supportedRealize σ α ha) :=
  fun _ _ h=>realizeDart_injective σ α ha (congrArg Subtype.val h)

lemma supportedRealize_surjective (he : 2*Nat.card (graph σ α ha).edgeSet=α.support.card) :
    Function.Surjective (supportedRealize σ α ha) := by
  apply ((Fintype.bijective_iff_injective_and_card (supportedRealize σ α ha)).mpr
    ⟨supportedRealize_injective σ α ha,?_⟩).surjective
  rw [Fintype.card_coe,SimpleGraph.dart_card_eq_twice_card_edges,
    SimpleGraph.edgeFinset_card,←Nat.card_eq_fintype_card]
  exact he

/-- When there are as many support darts as graph darts, no nonfixed dart is a
loop and no two different paired edges can realize the same simple edge. -/
lemma nonfixed_adj_of_edge_count
    (he : 2*Nat.card (graph σ α ha).edgeSet=α.support.card) {x : O} (hx : α x≠x) :
    (graph σ α ha).Adj (cycle σ x) (cycle σ (α x)) := by
  obtain ⟨d,hd⟩ := supportedRealize_surjective σ α ha he ⟨x,Equiv.Perm.mem_support.mpr hx⟩
  have hh : realizeDart σ α ha d=x := congrArg Subtype.val hd
  rw [←hh,realizeDart_fst,realizeDart_snd]
  exact d.adj

lemma dart_unique_of_edge_count (he : 2*Nat.card (graph σ α ha).edgeSet=α.support.card)
    {x y : O} (hx : α x≠x) (hy : α y≠y)
    (h₁ : cycle σ x=cycle σ y) (h₂ : cycle σ (α x)=cycle σ (α y)) : x=y := by
  obtain ⟨d,hd⟩ := supportedRealize_surjective σ α ha he ⟨x,Equiv.Perm.mem_support.mpr hx⟩
  obtain ⟨e,he'⟩ := supportedRealize_surjective σ α ha he ⟨y,Equiv.Perm.mem_support.mpr hy⟩
  have hh : realizeDart σ α ha d=x := congrArg Subtype.val hd
  have hq : realizeDart σ α ha e=y := congrArg Subtype.val he'
  have hde : d=e := by
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · rw [←realizeDart_fst σ α ha d,←realizeDart_fst σ α ha e,hh,hq]
      exact h₁
    · rw [←realizeDart_snd σ α ha d,←realizeDart_snd σ α ha e,hh,hq]
      exact h₂
  exact hh.symm.trans ((congrArg (realizeDart σ α ha) hde).trans hq)

lemma edge_count_of_tree_support (ht : (graph σ α ha).IsTree)
    (hs : α.support.card+2=2*Nat.card (Cycle σ)) :
    2*Nat.card (graph σ α ha).edgeSet=α.support.card := by
  have he := (SimpleGraph.isTree_iff_connected_and_card.mp ht).2
  omega

end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.TreeCentroid
open scoped Classical
open SimpleGraph
variable {V : Type} [Fintype V] {T : SimpleGraph V} (ht : T.IsTree)
    (H : SimpleGraph V) (hH : H≤T) (c n : V) (hn : ¬H.Adj c n)

include hH hn in
lemma branch_mem_iff_adj_of_avoid {x y : V} (he : H.Adj x y) :
    x∈branch ht c n ↔ y∈branch ht c n := by
  constructor
  · intro hx
    by_contra hy
    obtain ⟨rfl,rfl⟩ := branch_boundary ht hx hy (hH he)
    exact hn he.symm
  · intro hy
    by_contra hx
    obtain ⟨rfl,rfl⟩ := branch_boundary ht hy hx (hH he.symm)
    exact hn he

include hH hn in
lemma branch_mem_iff_reachable_of_avoid {x y : V} (hr : H.Reachable x y) :
    x∈branch ht c n ↔ y∈branch ht c n := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => rfl
  | cons e p ih => exact (branch_mem_iff_adj_of_avoid ht H hH c n hn e).trans ih

end TorsionFreeZeroDivisors.TreeCentroid

namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O]

lemma touchGraph_avoids_edge (σ φ γ : Equiv.Perm O) (hγ : Function.Involutive γ)
    (he : 2*Nat.card (graph φ γ hγ).edgeSet=γ.support.card)
    (S : Set (Cycle σ)) (d : O)
    (hd : cycle σ d∉S) (hd' : cycle σ (γ d)∉S) :
    ¬(touchGraph σ φ γ hγ S).Adj (cycle φ d) (cycle φ (γ d)) := by
  rintro ⟨hne,x,hx,hy,hS⟩
  have hdn : γ d≠d := fun h=>hne (by rw [h])
  have hxn : γ x≠x := fun h=>hne (hx.symm.trans (by rwa [h] at hy))
  have hxd := dart_unique_of_edge_count φ γ hγ he hxn hdn hx hy
  subst x
  exact hS.elim hd hd'

variable (σ α : Equiv.Perm O) (ha : Function.Involutive α)
    (T : SimpleGraph (Cycle σ)) (hT : T≤graph σ α ha)
    (hz : GenusZero σ α) (ht : T.IsTree)
local notation "β" => subgraphPair σ α ha T hT
local notation "γ" => α*β
local notation "φ" => α*σ
local notation "hγ" => complement_involutive α β ha (subgraphPair_involutive σ α ha T hT)
  (subgraphPair_subpairing σ α ha T hT)
local notation "D" => graph φ γ hγ
local notation "htD" => spanning_cotree_isTree σ α ha T hT hz ht

def cotreeSide (d : O) : Finset (Cycle φ) :=
  TreeCentroid.branch htD (cycle φ d) (cycle φ (γ d))

def fundamentalVertices (root : Cycle σ) (d : O) : Finset (Cycle σ) :=
  TreeCentroid.rootPath ht root (cycle σ d) ∪ TreeCentroid.rootPath ht root (cycle σ (α d))

omit [Fintype O] in
lemma root_mem_fundamentalVertices (root : Cycle σ) (d : O) :
    root∈fundamentalVertices σ α T ht root d :=
  Finset.mem_union_left _ (TreeCentroid.root_mem_rootPath ht _ _)

lemma endpoints_not_descendants {root v : Cycle σ} {d : O}
    (hv : v∉fundamentalVertices σ α T ht root d) :
    cycle σ d∉TreeCentroid.descendants ht root v ∧
    cycle σ (γ d)∉TreeCentroid.descendants ht root v := by
  have hvr : v≠root := fun he=>hv (he ▸ root_mem_fundamentalVertices σ α T ht root d)
  have h₁ : cycle σ d∉TreeCentroid.descendants ht root v := by
    intro h
    apply hv
    apply Finset.mem_union_left
    simpa only [TreeCentroid.rootPath,List.mem_toFinset] using
      (TreeCentroid.descendant_mem_root_path ht hvr h)
  have h₂ : cycle σ (α d)∉TreeCentroid.descendants ht root v := by
    intro h
    apply hv
    apply Finset.mem_union_right
    simpa only [TreeCentroid.rootPath,List.mem_toFinset] using
      (TreeCentroid.descendant_mem_root_path ht hvr h)
  refine ⟨h₁,?_⟩
  rcases complement_subpairing α β ha (subgraphPair_subpairing σ α ha T hT) d with h|h
  · rwa [h]
  · rwa [h]

/-- Outside the two actual root paths, all incident faces of a primal vertex
lie on the same side of the deleted cotree edge. -/
theorem outside_fundamental_sameSide {root v : Cycle σ} {d x y : O}
    (hv : v∉fundamentalVertices σ α T ht root d)
    (hx : cycle σ x=v) (hy : cycle σ y=v) :
    cycle φ x∈cotreeSide σ α ha T hT hz ht d ↔
    cycle φ y∈cotreeSide σ α ha T hT hz ht d := by
  have hvr : v≠root := fun he=>hv (he ▸ root_mem_fundamentalVertices σ α T ht root d)
  let S : Set (Cycle σ) := ↑(TreeCentroid.descendants ht root v)
  have hs : v∈S := TreeCentroid.self_mem_descendants ht hvr
  have hh := branch_dual_touch_connected σ α ha T hT ht hz
    (TreeCentroid.next_adj ht hvr) (hx ▸ hs) (hy ▸ hs)
  have he := edge_count_of_tree_support φ γ hγ htD (cotree_support σ α ha T hT hz ht)
  obtain ⟨hd,hd'⟩ := endpoints_not_descendants σ α ha T hT ht hv
  exact TreeCentroid.branch_mem_iff_reachable_of_avoid htD
    (touchGraph σ φ γ hγ S) (touchGraph_le σ φ γ hγ S)
    (cycle φ d) (cycle φ (γ d))
    (touchGraph_avoids_edge σ φ γ hγ he S d hd hd') hh

omit [Fintype O] in
/-- Endpoints of a primal edge have incident occurrences on a common face. -/
lemma edge_common_face (x : O) : cycle φ (σ.symm x)=cycle φ (α x) := by
  have hf := cycle_apply φ (σ.symm x)
  simpa only [Equiv.Perm.mul_apply,Equiv.apply_symm_apply] using hf.symm

/-- The two-root-path vertex set really separates the corresponding dual sides,
including original loops, parallel edges, and tree edges. -/
theorem fundamental_no_crossing {root : Cycle σ} {d : O} {v w : Cycle σ}
    (hv : v∉fundamentalVertices σ α T ht root d)
    (hw : w∉fundamentalVertices σ α T ht root d)
    (he : (graph σ α ha).Adj v w) {x y : O}
    (hx : cycle σ x=v) (hy : cycle σ y=w) :
    cycle φ x∈cotreeSide σ α ha T hT hz ht d ↔
    cycle φ y∈cotreeSide σ α ha T hT hz ht d := by
  obtain ⟨_,z,hzv,hzw⟩ := he
  have hzv' : cycle σ (σ.symm z)=v := by
    rw [←cycle_apply σ (σ.symm z),σ.apply_symm_apply]
    exact hzv
  have h₁ := outside_fundamental_sameSide σ α ha T hT hz ht hv hx hzv'
  have h₂ := outside_fundamental_sameSide σ α ha T hT hz ht hw hzw hy
  rw [edge_common_face σ α z] at h₁
  exact h₁.trans h₂

end TorsionFreeZeroDivisors.MapEuler

end

end OAI
