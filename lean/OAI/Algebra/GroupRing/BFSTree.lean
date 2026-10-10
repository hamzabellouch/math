import Mathlib
import OAI.Algebra.GroupRing.ConedMap

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ConedMap
open scoped Classical
open PermutationCycles MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (ha : Function.Involutive α)
local notation "ρ" => rotation σ α
local notation "π" => pairing α
local notation "G" => graph σ α ha
local notation "G'" => graph ρ π (pairing_involutive α ha)

def oldVertex (v : Cycle σ) : Cycle ρ := (vertexEquiv σ α).symm (.inl v)
def centerVertex (f : Cycle (α*σ)) : Cycle ρ := (vertexEquiv σ α).symm (.inr f)
lemma oldVertex_injective : Function.Injective (oldVertex σ α) :=
  (vertexEquiv σ α).symm.injective.comp Sum.inl_injective
lemma centerVertex_injective : Function.Injective (centerVertex σ α) :=
  (vertexEquiv σ α).symm.injective.comp Sum.inr_injective
lemma old_ne_center (v : Cycle σ) (f : Cycle (α*σ)) : oldVertex σ α v≠centerVertex σ α f := by
  intro he
  have hh := (vertexEquiv σ α).symm.injective he
  exact Sum.inl_ne_inr hh

@[simp] lemma oldVertex_cycle (x : O) : oldVertex σ α (cycle σ x)=cycle ρ (old x) := rfl
@[simp] lemma centerVertex_cycle (x : O) : centerVertex σ α (cycle (α*σ) x)=cycle ρ (center x) := rfl

lemma old_adj {v w : Cycle σ} (he : (G).Adj v w) : (G').Adj (oldVertex σ α v) (oldVertex σ α w) := by
  obtain ⟨hne,x,hx,hy⟩ := he
  refine ⟨(oldVertex_injective σ α).ne hne,old x,?_,?_⟩
  · rw [←oldVertex_cycle,hx]
  · rw [pairing_old,←oldVertex_cycle,hy]

lemma radial_adj (x : O) : (G').Adj (oldVertex σ α (cycle σ x))
    (centerVertex σ α (cycle (α*σ) x)) := by
  refine ⟨old_ne_center σ α _ _,radial x,?_,?_⟩
  · rw [vertex_radial,oldVertex_cycle]
  · rw [pairing_radial,centerVertex_cycle]

def oldHom : G →g G' := ⟨oldVertex σ α,fun h=>old_adj σ α ha h⟩

theorem connected (hc : (G).Connected) : (G').Connected := by
  apply connected_of_component_card_one
  rw [Nat.card_congr (componentEquiv σ α)]
  exact component_card_one_of_connected σ α ha hc

lemma old_distance_le (hc : (G).Connected) (v w : Cycle σ) :
    (G').dist (oldVertex σ α v) (oldVertex σ α w)≤(G).dist v w := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist v w
  have hh := (G').dist_le (p.map (oldHom σ α ha))
  rwa [SimpleGraph.Walk.length_map,hp] at hh

lemma center_distance_le (hc : (G).Connected) (root : Cycle σ) (r : ℕ)
    (hr : ∀ v,(G).dist root v≤r) (f : Cycle (α*σ)) :
    (G').dist (oldVertex σ α root) (centerVertex σ α f)≤r+1 := by
  obtain ⟨x,rfl⟩ := cycle_surjective (α*σ) f
  have hh := (connected σ α ha hc).dist_triangle
    (u:=oldVertex σ α root) (v:=oldVertex σ α (cycle σ x))
    (w:=centerVertex σ α (cycle (α*σ) x))
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr (radial_adj σ α ha x)] at hh
  exact hh.trans (Nat.add_le_add_right ((old_distance_le σ α ha hc _ _).trans (hr _)) _)

def oldEmbedding : Cycle σ ↪ Cycle ρ := ⟨oldVertex σ α,oldVertex_injective σ α⟩
def liftSet (s : Finset (Cycle σ)) : Finset (Cycle ρ) := s.map (oldEmbedding σ α)
lemma liftSet_card (s : Finset (Cycle σ)) : (liftSet σ α s).card=s.card := Finset.card_map _
lemma old_mem_liftSet (s : Finset (Cycle σ)) (v : Cycle σ) :
    oldVertex σ α v∈liftSet σ α s ↔ v∈s := Finset.mem_map' (oldEmbedding σ α)
lemma center_not_liftSet (s : Finset (Cycle σ)) (f : Cycle (α*σ)) :
    centerVertex σ α f∉liftSet σ α s := by
  intro hf
  obtain ⟨v,_,hv⟩ := Finset.mem_map.mp hf
  exact old_ne_center σ α v f hv

/-- Distances to zero-cost auxiliary centers incur one extra step, but all
original vertices remain within the original radius. -/
theorem distance_cost (hc : (G).Connected) (root : Cycle σ) (r : ℕ)
    (hr : ∀ v,(G).dist root v≤r) (v : Cycle ρ) :
    (G').dist (oldVertex σ α root) v + (if v∈liftSet σ α Finset.univ then 1 else 0)≤r+1 := by
  obtain ⟨q,rfl⟩ := (vertexEquiv σ α).symm.surjective v
  rcases q with v|f
  · change (G').dist (oldVertex σ α root) (oldVertex σ α v)+
      (if oldVertex σ α v∈liftSet σ α Finset.univ then 1 else 0)≤r+1
    rw [ite_eq_left ((old_mem_liftSet σ α Finset.univ v).mpr (Finset.mem_univ _))]
    exact Nat.add_le_add_right ((old_distance_le σ α ha hc root v).trans (hr v)) _
  · change (G').dist (oldVertex σ α root) (centerVertex σ α f)+
      (if centerVertex σ α f∈liftSet σ α Finset.univ then 1 else 0)≤r+1
    rw [ite_eq_right (center_not_liftSet σ α Finset.univ f),Nat.add_zero]
    exact center_distance_le σ α ha hc root r hr f

end TorsionFreeZeroDivisors.ConedMap

/-! A literal breadth-first spanning tree, with its distances and radius
preserved. This is the rooted tree used in the sharp planar separator. -/
namespace TorsionFreeZeroDivisors.BFSTree
open scoped Classical
open SimpleGraph
variable {V : Type} (G : SimpleGraph V) (hc : G.Connected) (root : V)

include hc in
lemma exists_parent (v : V) (hv : v≠root) :
    ∃ u,G.Adj v u ∧ G.dist u root+1=G.dist v root := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist v root
  cases p with
  | nil => exact (hv rfl).elim
  | @cons v u root h p =>
    refine ⟨u,h,?_⟩
    have h₁ := G.dist_le p
    have h₂ := hc.dist_triangle (u:=v) (v:=u) (w:=root)
    rw [G.dist_eq_one_iff_adj.mpr h] at h₂
    simp only [Walk.length_cons] at hp
    omega

def parent (v : V) : V := if hv : v=root then root else (exists_parent G hc root v hv).choose
lemma parent_adj (v : V) (hv : v≠root) : G.Adj v (parent G hc root v) := by
  rw [parent,dite_eq_right hv]
  exact (exists_parent G hc root v hv).choose_spec.1
lemma parent_dist (v : V) (hv : v≠root) :
    G.dist (parent G hc root v) root+1=G.dist v root := by
  rw [parent,dite_eq_right hv]
  exact (exists_parent G hc root v hv).choose_spec.2
lemma parent_ne (v : V) (hv : v≠root) : parent G hc root v≠v := (parent_adj G hc root v hv).ne'

def tree : SimpleGraph V where
  Adj v w := (v≠root ∧ parent G hc root v=w) ∨ (w≠root ∧ parent G hc root w=v)
  symm := ⟨fun _ _ h=>h.elim Or.inr Or.inl⟩
  loopless := ⟨fun v h=>h.elim (fun h=>parent_ne G hc root v h.1 h.2)
    (fun h=>parent_ne G hc root v h.1 h.2)⟩

lemma tree_le : tree G hc root≤G := by
  intro v w h
  rcases h with ⟨hv,h⟩|⟨hw,h⟩
  · rw [←h]
    exact parent_adj G hc root v hv
  · rw [←h]
    exact (parent_adj G hc root w hw).symm

lemma exists_tree_walk (v : V) :
    ∃ p : (tree G hc root).Walk v root,p.length=G.dist v root := by
  generalize hn : G.dist v root=n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hv : v=root
    · subst v
      exact ⟨Walk.nil,by simp only [Walk.length_nil,dist_self] at hn ⊢; omega⟩
    · have hp := parent_dist G hc root v hv
      obtain ⟨p,hl⟩ := ih (G.dist (parent G hc root v) root) (by omega)
        (parent G hc root v) rfl
      have he : (tree G hc root).Adj v (parent G hc root v) := Or.inl ⟨hv,rfl⟩
      exact ⟨Walk.cons he p,by rw [Walk.length_cons,hl];omega⟩

lemma connected : (tree G hc root).Connected := by
  have : Nonempty V := ⟨root⟩
  refine ⟨fun v w=>?_⟩
  obtain ⟨p,_⟩ := exists_tree_walk G hc root v
  obtain ⟨q,_⟩ := exists_tree_walk G hc root w
  exact ⟨p.append q.reverse⟩

/-- All root distances are unchanged, not merely bounded by an abstract height. -/
theorem dist_root (v : V) : (tree G hc root).dist v root=G.dist v root := by
  apply Nat.le_antisymm
  · obtain ⟨p,hp⟩ := exists_tree_walk G hc root v
    rw [←hp]
    exact (tree G hc root).dist_le p
  · exact Reachable.dist_anti (tree_le G hc root) ((connected G hc root) v root)

def parentEdge (v : {v : V // v≠root}) : (tree G hc root).edgeSet :=
  ⟨s(v.val,parent G hc root v.val),Or.inl ⟨v.property,rfl⟩⟩
lemma parentEdge_surjective : Function.Surjective (parentEdge G hc root) := by
  rintro ⟨e,he⟩
  induction e using Sym2.inductionOn with
  | _ v w =>
    rcases he with ⟨hv,h⟩|⟨hw,h⟩
    · refine ⟨⟨v,hv⟩,Subtype.ext ?_⟩
      change s(v,parent G hc root v)=s(v,w)
      rw [h]
    · refine ⟨⟨w,hw⟩,Subtype.ext ?_⟩
      change s(w,parent G hc root w)=s(v,w)
      rw [h,Sym2.eq_swap]

variable [Fintype V]
/-- The parent edges form an actual spanning tree of the original graph. -/
theorem isTree : (tree G hc root).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨connected G hc root,?_⟩
  have hl := Fintype.card_le_of_surjective _ (parentEdge_surjective G hc root)
  have hr := (connected G hc root).card_vert_le_card_edgeSet_add_one
  have hcard : Fintype.card {v : V // v≠root}+1=Fintype.card V := by
    simpa only [Fintype.card_subtype_compl,Fintype.card_unique] using
      Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ⟨root⟩)
  rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card] at hl hcard
  omega

end TorsionFreeZeroDivisors.BFSTree

namespace TorsionFreeZeroDivisors.TreeCentroid
open scoped Classical
open SimpleGraph
variable {V : Type} [Fintype V] {T : SimpleGraph V} (ht : T.IsTree)

omit [Fintype V] in
lemma rootPath_cost (budget : Finset V) (root v : V) (r : ℕ)
    (hr : T.dist root v+(if v∈budget then 1 else 0)≤r+1) :
    ((rootPath ht root v)∩budget).card≤r+1 := by
  by_cases hv : v∈budget
  · have hh := Finset.card_le_card (show rootPath ht root v∩budget⊆rootPath ht root v from Finset.inter_subset_left)
    rw [rootPath_card] at hh
    rw [ite_eq_left hv] at hr
    omega
  · have hs : rootPath ht root v∩budget⊆(rootPath ht root v).erase v := by
      intro x hx
      obtain ⟨hx,hxb⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_erase.mpr ⟨fun he=>hv (he ▸ hxb),hx⟩
    have hh := Finset.card_le_card hs
    rw [Finset.card_erase_of_mem (self_mem_rootPath ht root v),rootPath_card] at hh
    rw [ite_eq_right hv] at hr
    omega

omit [Fintype V] in
/-- Zero-cost face centers may be introduced for triangulation without losing
the sharp original-vertex bound. Only original vertices are charged. -/
theorem two_root_paths_cost (budget : Finset V) (root v w : V) (r : ℕ)
    (hroot : root∈budget)
    (hv : T.dist root v+(if v∈budget then 1 else 0)≤r+1)
    (hw : T.dist root w+(if w∈budget then 1 else 0)≤r+1) :
    ((rootPath ht root v∪rootPath ht root w)∩budget).card≤2*r+1 := by
  have h₁ := rootPath_cost ht budget root v r hv
  have h₂ := rootPath_cost ht budget root w r hw
  have hp : 0<((rootPath ht root v∩budget)∩(rootPath ht root w∩budget)).card :=
    Finset.card_pos.mpr ⟨root,Finset.mem_inter.mpr
      ⟨Finset.mem_inter.mpr ⟨root_mem_rootPath ht root v,hroot⟩,
       Finset.mem_inter.mpr ⟨root_mem_rootPath ht root w,hroot⟩⟩⟩
  rw [Finset.union_inter_distrib_right]
  have hh := Finset.card_union_add_card_inter (rootPath ht root v∩budget) (rootPath ht root w∩budget)
  omega

omit [Fintype V] in
lemma two_root_paths_cost_erase_root (budget : Finset V) (root v w : V) (r : ℕ)
    (hroot : root∈budget)
    (hv : T.dist root v+(if v∈budget then 1 else 0)≤r+1)
    (hw : T.dist root w+(if w∈budget then 1 else 0)≤r+1) :
    (((rootPath ht root v∪rootPath ht root w)∩budget).erase root).card≤2*r := by
  have hc := two_root_paths_cost ht budget root v w r hroot hv hw
  have hm : root∈(rootPath ht root v∪rootPath ht root w)∩budget :=
    Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (root_mem_rootPath ht _ _),hroot⟩
  rw [Finset.card_erase_of_mem hm]
  omega

end TorsionFreeZeroDivisors.TreeCentroid

namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O]

/-- The exact bounded-radius separator on a genus-zero rotation map.  The
partition balances any chosen set of unit-weight vertices.  In particular the
root is charged once, so deleting a contracted root saves one unit. -/
theorem radius_separator (σ α : Equiv.Perm O) (ha : Function.Involutive α)
    (hz : GenusZero σ α) (hc : (graph σ α ha).Connected)
    (root : Cycle σ) (r : ℕ) (hr : ∀ v,(graph σ α ha).dist root v≤r)
    (active : Finset (Cycle σ)) :
    ∃ cut side : Finset (Cycle σ), root∈cut ∧ cut.card≤2*r+1 ∧
      (cut.erase root).card≤2*r ∧
      3*(active.filter (fun v=>v∉cut ∧ v∈side)).card≤2*active.card ∧
      3*(active.filter (fun v=>v∉cut ∧ v∉side)).card≤2*active.card ∧
      ∀ v w,v∉cut→w∉cut→(graph σ α ha).Adj v w→(v∈side↔w∈side) := by
  classical
  let ρ := ConedMap.rotation σ α
  let π := ConedMap.pairing α
  have hπ := ConedMap.pairing_involutive α ha
  let g := graph ρ π hπ
  have hgc : g.Connected := ConedMap.connected σ α ha hc
  let e := ConedMap.oldEmbedding σ α
  let u := e root
  let T := BFSTree.tree g hgc u
  have hT : T≤g := BFSTree.tree_le g hgc u
  have ht : T.IsTree := BFSTree.isTree g hgc u
  have hz' : GenusZero ρ π := ConedMap.genusZero σ α hz
  have htri : ∀ c : Cycle (π*ρ),(members (π*ρ) c).card≤3 :=
    fun c=>(ConedMap.triangular σ α c).le
  let a := ConedMap.liftSet σ α active
  obtain ⟨d,h₁,h₂⟩ := triangular_balanced_fundamental ρ π hπ T hT hz' ht a u htri
  let F := fundamentalVertices ρ π T ht u d
  let D := cotreeSide ρ π hπ T hT hz' ht d
  let cut := Finset.univ.filter (fun v=>e v∈F)
  let side := Finset.univ.filter (fun v=>homeFace ρ π (e v)∈D)
  have hcut (v : Cycle σ) : v∈cut↔e v∈F := by simp only [cut,Finset.mem_filter,Finset.mem_univ,true_and]
  have hside (v : Cycle σ) : v∈side↔homeFace ρ π (e v)∈D := by
    simp only [side,Finset.mem_filter,Finset.mem_univ,true_and]
  have hroot : root∈cut := (hcut root).mpr (root_mem_fundamentalVertices ρ π T ht u d)
  let budget : Finset (Cycle ρ) := ConedMap.liftSet σ α Finset.univ
  have hcost (v : Cycle ρ) : T.dist u v+(if v∈budget then 1 else 0)≤r+1 := by
    rw [SimpleGraph.dist_comm,BFSTree.dist_root,SimpleGraph.dist_comm]
    exact ConedMap.distance_cost σ α ha hc root r hr v
  have hmap : cut.map e=F∩ConedMap.liftSet σ α Finset.univ := by
    ext v
    simp only [Finset.mem_map,Finset.mem_inter,ConedMap.liftSet,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨(hcut x).mp hx,⟨x,rfl⟩⟩
    · rintro ⟨hv,x,rfl⟩
      exact ⟨x,(hcut x).mpr hv,rfl⟩
  have hcard : cut.card≤2*r+1 := by
    rw [←Finset.card_map (f:=e),hmap]
    have hh := TreeCentroid.two_root_paths_cost ht budget
      u (cycle ρ d) (cycle ρ (π d)) r
      ((ConedMap.old_mem_liftSet σ α Finset.univ root).mpr (Finset.mem_univ _)) (by convert hcost (cycle ρ d) using 1; congr 2) (by convert hcost (cycle ρ (π d)) using 1; congr 2)
    convert hh using 1
    congr 1
    ext v
    simp only [F,budget,fundamentalVertices,Finset.mem_inter,Finset.mem_union,TreeCentroid.rootPath,List.mem_toFinset]
  have hfilter (p : Cycle ρ→Prop) [DecidablePred p] :
      (active.filter (fun v=>p (e v))).card=(a.filter p).card := by
    rw [←Finset.card_map (f:=e)]
    congr 1
    ext v
    simp only [Finset.mem_map,Finset.mem_filter]
    constructor
    · rintro ⟨x,⟨hx,hp⟩,rfl⟩
      exact ⟨Finset.mem_map.mpr ⟨x,hx,rfl⟩,hp⟩
    · rintro ⟨hv,hp⟩
      obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hv
      exact ⟨x,⟨hx,hp⟩,rfl⟩
  refine ⟨cut,side,hroot,hcard,?_,?_,?_,?_⟩
  · rw [Finset.card_erase_of_mem hroot]
    omega
  · have he : active.filter (fun v=>v∉cut ∧ v∈side)=
        active.filter (fun v=>e v∉F ∧ homeFace ρ π (e v)∈D) := by
      ext v
      simp only [Finset.mem_filter,hcut,hside]
    rw [he,hfilter (fun v=>v∉F ∧ homeFace ρ π v∈D),←ConedMap.liftSet_card σ α active]
    exact h₁
  · have he : active.filter (fun v=>v∉cut ∧ v∉side)=
        active.filter (fun v=>e v∉F ∧ homeFace ρ π (e v)∉D) := by
      ext v
      simp only [Finset.mem_filter,hcut,hside]
    rw [he,hfilter (fun v=>v∉F ∧ homeFace ρ π v∉D),←ConedMap.liftSet_card σ α active]
    exact h₂
  · intro v w hv hw he
    rw [hside,hside]
    exact fundamental_no_crossing ρ π hπ T hT hz' ht
      (fun h=>hv ((hcut v).mpr h)) (fun h=>hw ((hcut w).mpr h))
      (ConedMap.old_adj σ α ha he) (home_cycle ρ (e v)) (home_cycle ρ (e w))

end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.MapRestrict
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (f : Equiv.Perm O) (P : O→Prop) (hf : ∀ x,P (f x)↔P x)

def perm : Equiv.Perm {x // P x} := f.subtypeEquiv (fun x=>(hf x).symm)
omit [Fintype O] in
@[simp] lemma perm_val (x : {x // P x}) : (perm f P hf x).val=f x := rfl
omit [Fintype O] in
include hf in
lemma not_invariant (x : O) : (¬P (f x))↔¬P x := not_congr (hf x)
local notation "fP" => perm f P hf
local notation "fN" => perm f (fun x=>¬P x) (not_invariant f P hf)

def cycleInclude : Cycle fP→Cycle f :=
  PermutationCycles.lift fP (fun x=>cycle f x.val) (fun x=>cycle_apply f x.val)
@[simp] lemma cycleInclude_cycle (x : {x // P x}) : cycleInclude f P hf (cycle fP x)=cycle f x.val := rfl

def cycleRaw (x : O) : Cycle fP ⊕ Cycle fN :=
  if h:P x then .inl (cycle fP ⟨x,h⟩) else .inr (cycle fN ⟨x,h⟩)
omit [Fintype O] in
lemma cycleRaw_apply (x : O) : cycleRaw f P hf (f x)=cycleRaw f P hf x := by
  by_cases hx : P x
  · rw [cycleRaw,dite_eq_left ((hf x).mpr hx),cycleRaw,dite_eq_left hx]
    exact congrArg Sum.inl (cycle_apply fP ⟨x,hx⟩)
  · rw [cycleRaw,dite_eq_right (fun h=>hx ((hf x).mp h)),cycleRaw,dite_eq_right hx]
    exact congrArg Sum.inr (cycle_apply fN ⟨x,hx⟩)

def cycleEquiv : Cycle f≃Cycle fP ⊕ Cycle fN where
  toFun := PermutationCycles.lift f (cycleRaw f P hf) (cycleRaw_apply f P hf)
  invFun := Sum.elim (cycleInclude f P hf) (cycleInclude f (fun x=>¬P x) (not_invariant f P hf))
  left_inv := by
    intro c
    obtain ⟨x,rfl⟩ := cycle_surjective f c
    change (Sum.elim _ _) (cycleRaw f P hf x)=cycle f x
    unfold cycleRaw
    split_ifs <;> rfl
  right_inv := by
    intro c
    rcases c with c|c
    · obtain ⟨x,rfl⟩ := cycle_surjective fP c
      change cycleRaw f P hf x.val=Sum.inl (cycle fP x)
      rw [cycleRaw,dite_eq_left x.property]
    · obtain ⟨x,rfl⟩ := cycle_surjective fN c
      change cycleRaw f P hf x.val=Sum.inr (cycle fN x)
      rw [cycleRaw,dite_eq_right x.property]

lemma cycle_card : Nat.card (Cycle f)=Nat.card (Cycle fP)+Nat.card (Cycle fN) := by
  rw [Nat.card_congr (cycleEquiv f P hf),Nat.card_sum]
omit [Fintype O] in
lemma perm_involutive (hi : Function.Involutive f) : Function.Involutive fP :=
  fun x=>Subtype.ext (hi x.val)

def supportEquiv : {x : O // f x≠x} ≃
    {x : Subtype P // fP x≠x} ⊕ {x : {x // ¬P x} // fN x≠x} where
  toFun x := if h:P x.val then .inl ⟨⟨x.val,h⟩,fun he=>x.property (congrArg Subtype.val he)⟩
    else .inr ⟨⟨x.val,h⟩,fun he=>x.property (congrArg Subtype.val he)⟩
  invFun := Sum.elim (fun x=>⟨x.val.val,fun he=>x.property (Subtype.ext he)⟩)
    (fun x=>⟨x.val.val,fun he=>x.property (Subtype.ext he)⟩)
  left_inv := by intro x;dsimp;split_ifs <;> rfl
  right_inv := by
    intro x
    rcases x with x|x
    · dsimp
      rw [dite_eq_left x.val.property]
    · dsimp
      rw [dite_eq_right x.val.property]

lemma support_card : f.support.card=(fP).support.card+(fN).support.card := by
  simp only [ConedMap.support_card_nat]
  rw [Nat.card_congr (supportEquiv f P hf),Nat.card_sum]

end TorsionFreeZeroDivisors.MapRestrict

end

end OAI
