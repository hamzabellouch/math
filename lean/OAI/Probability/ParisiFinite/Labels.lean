import Mathlib
import OAI.Probability.ParisiFinite.UsedVertices

namespace OAI

/-! Labels. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped BigOperators

namespace BoundedBranch

 
def labels (n : ℕ) : (h : ℕ) → Tree n h → Multiset (Fin n)
  | 0, _ => 0
  | h+1, b => ∑i, (b i).elim 0 (fun c => {i}+labels n h c)

def links (n : ℕ) : (h : ℕ) → Fin n → Tree n h → Multiset (Fin n × Fin n)
  | 0, _, _ => 0
  | h+1, i, b => ∑j, (b j).elim 0 (fun c => {(i,j)}+links n h j c)

@[simp] theorem card_labels (n h : ℕ) (b : Tree n h) : (labels n h b).card=size n h b := by
  induction h with
  | zero => rfl
  | succ h ih =>
    change (∑i, (b i).elim 0 (fun c => {i}+labels n h c)).card=_
    rw [Multiset.card_sum]
    apply Finset.sum_congr rfl
    intro i hi
    cases hb : b i with
    | none => rfl
    | some c => simp [ih,add_comm]

@[simp] theorem map_snd_links (n h : ℕ) (i : Fin n) (b : Tree n h) :
    (links n h i b).map Prod.snd=labels n h b := by
  induction h generalizing i with
  | zero => rfl
  | succ h ih =>
    change (∑j,(b j).elim 0 (fun c => {(i,j)}+links n h j c)).map Prod.snd=_
    rw [show (∑j,(b j).elim 0 (fun c => {(i,j)}+links n h j c)).map Prod.snd =
        ∑j,((b j).elim 0 (fun c => {(i,j)}+links n h j c)).map Prod.snd from
        map_sum (Multiset.mapAddMonoidHom Prod.snd) _ _]
    apply Finset.sum_congr rfl
    intro j hj
    cases hb : b j with
    | none => rfl
    | some c => simp [ih]

@[simp] theorem card_links (n h : ℕ) (i : Fin n) (b : Tree n h) :
    (links n h i b).card=size n h b := by
  rw [←card_labels n h b,←map_snd_links n h i b,Multiset.card_map]

 
def unfoldTree {n : ℕ} (U S : Finset (Fin n)) (parent : Fin n → Fin n) :
    (h : ℕ) → Fin n → Tree n h
  | 0, _ => ()
  | h+1, i => fun j => if j∈U\S ∧ parent j=i then some (unfoldTree U S parent h j) else none

namespace Parent
variable {n : ℕ} (U S : Finset (Fin n)) (parent : Fin n → Fin n) (rank : Fin n → ℕ)

def layer (k : ℕ) : Finset (Fin n) := U.filter (fun i => rank i=k)

lemma labels_unfold (h : ℕ) (i : Fin n) :
    labels n (h+1) (unfoldTree U S parent (h+1) i)=
      ∑j:Fin n, if j∈U\S ∧ parent j=i then
        {j}+labels n h (unfoldTree U S parent h j) else 0 := by
  apply Finset.sum_congr rfl
  intro j hj
  simp only [unfoldTree]
  split_ifs <;> rfl

lemma links_unfold (h : ℕ) (i : Fin n) :
    links n (h+1) i (unfoldTree U S parent (h+1) i)=
      ∑j:Fin n, if j∈U\S ∧ parent j=i then
        {(i,j)}+links n h j (unfoldTree U S parent h j) else 0 := by
  apply Finset.sum_congr rfl
  intro j hj
  simp only [unfoldTree]
  split_ifs <;> rfl

variable (hS : S⊆U) (hzero : ∀i∈U, rank i=0 ↔ i∈S)
  (hparent : ∀j∈U\S, parent j∈U ∧ rank (parent j)+1=rank j)

include hzero hparent in
lemma child_layer_iff (k : ℕ) (j : Fin n) :
    j∈U\S ∧ parent j∈layer U rank k ↔ j∈layer U rank (k+1) := by
  constructor
  · rintro ⟨hj,hp⟩
    rcases Finset.mem_sdiff.mp hj with ⟨hjU,hjS⟩
    rcases Finset.mem_filter.mp hp with ⟨hpU,hpk⟩
    exact Finset.mem_filter.mpr ⟨hjU,by rw [←(hparent j (by simp [hjU,hjS])).2,hpk]⟩
  · intro hj
    rcases Finset.mem_filter.mp hj with ⟨hjU,hjrank⟩
    have hjS : j∉S := by
      intro hjS
      have := (hzero j hjU).mpr hjS
      omega
    have hp := hparent j (Finset.mem_sdiff.mpr ⟨hjU,hjS⟩)
    refine ⟨Finset.mem_sdiff.mpr ⟨hjU,hjS⟩,Finset.mem_filter.mpr ⟨hp.1,?_⟩⟩
    omega

include hzero hparent in
 

theorem sum_labels_layer (h k : ℕ) :
    (∑i∈layer U rank k, labels n h (unfoldTree U S parent h i))=
      ∑j∈U, if k<rank j ∧ rank j ≤ k+h then ({j}:Multiset (Fin n)) else 0 := by
  induction h generalizing k with
  | zero =>
    simp only [labels,Finset.sum_const_zero,Nat.add_zero]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    exact ite_eq_right (by omega)
  | succ h ih =>
    simp_rw [labels_unfold]
    rw [Finset.sum_comm]
    have ht (j : Fin n) : (∑i∈layer U rank k, if j∈U\S ∧ parent j=i then
        ({j}:Multiset (Fin n))+labels n h (unfoldTree U S parent h j) else 0)=
        if j∈layer U rank (k+1) then {j}+labels n h (unfoldTree U S parent h j) else 0 := by
      by_cases hj : j∈U\S
      · simp only [hj,true_and,Finset.sum_ite_eq]
        congr 1
        exact propext (by simpa only [hj,true_and] using child_layer_iff U S parent rank hzero hparent k j)
      · have hjL : j∉layer U rank (k+1) := by
          intro hh
          exact hj ((child_layer_iff U S parent rank hzero hparent k j).mpr hh).1
        simp [hj,hjL]
    simp_rw [ht]
    rw [←Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
    rw [Finset.sum_add_distrib,ih]
    rw [layer,Finset.sum_filter]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h₁ : rank j=k+1
    · simp [h₁]
    · have hr : (k<rank j ∧ rank j≤k+(h+1)) ↔ (k+1<rank j ∧ rank j≤k+1+h) := by omega
      simp only [h₁,ite_false,zero_add,hr]

include hS hzero hparent in
 
theorem sum_labels_roots (h : ℕ) (hbound : ∀j∈U, rank j≤h) :
    (∑i∈S,labels n h (unfoldTree U S parent h i))=(U\S).val := by
  have hL : layer U rank 0=S := by
    ext i
    simp only [layer,Finset.mem_filter]
    constructor
    · rintro ⟨hi,hr⟩
      exact (hzero i hi).mp hr
    · intro hi
      exact ⟨hS hi,(hzero i (hS hi)).mpr hi⟩
  calc
    _ = ∑i∈layer U rank 0,labels n h (unfoldTree U S parent h i) := by rw [hL]
    _ = ∑j∈U, if 0<rank j ∧ rank j≤0+h then ({j}:Multiset (Fin n)) else 0 :=
      sum_labels_layer U S parent rank hzero hparent h 0
    _ = (U\S).val := by
      have he (j : Fin n) (hj : j∈U) :
          (0<rank j ∧ rank j≤0+h) ↔ j∉S := by
        have hz := hzero j hj
        have hb := hbound j hj
        constructor
        · rintro ⟨hr,_⟩ hjS
          have := hz.mpr hjS
          omega
        · intro hjS
          exact ⟨Nat.pos_of_ne_zero (fun hr => hjS (hz.mp hr)),by simpa using hb⟩
      have hh : (∑j∈U, if 0<rank j ∧ rank j≤0+h then ({j}:Multiset (Fin n)) else 0)=
          ∑j∈U\S, ({j}:Multiset (Fin n)) := by
        rw [Finset.sdiff_eq_filter,Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [he j hj]
      rw [hh]
      exact Finset.sum_multiset_singleton _

lemma links_eq_map_labels (h : ℕ) (i : Fin n) :
    links n h i (unfoldTree U S parent h i)=
      (labels n h (unfoldTree U S parent h i)).map (fun j => (parent j,j)) := by
  induction h generalizing i with
  | zero => rfl
  | succ h ih =>
    rw [links_unfold,labels_unfold]
    rw [show (∑j:Fin n,if j∈U\S ∧ parent j=i then
          ({j}:Multiset (Fin n))+labels n h (unfoldTree U S parent h j) else 0).map
          (fun j => (parent j,j)) =
        ∑j:Fin n,(if j∈U\S ∧ parent j=i then
          ({j}:Multiset (Fin n))+labels n h (unfoldTree U S parent h j) else 0).map
          (fun j => (parent j,j)) from
        map_sum (Multiset.mapAddMonoidHom (fun j => (parent j,j))) _ _]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hp : j∈U\S ∧ parent j=i
    · simp [hp,ih]
    · rw [ite_eq_right hp,ite_eq_right hp]; rfl

include hS hzero hparent in
 
theorem sum_links_roots (h : ℕ) (hbound : ∀j∈U, rank j≤h) :
    (∑i∈S,links n h i (unfoldTree U S parent h i))=
      (U\S).val.map (fun j => (parent j,j)) := by
  rw [←sum_labels_roots U S parent rank hS hzero hparent h hbound]
  rw [show (∑i∈S, labels n h (unfoldTree U S parent h i)).map (fun j => (parent j,j))=
      ∑i∈S, (labels n h (unfoldTree U S parent h i)).map (fun j => (parent j,j)) from
    map_sum (Multiset.mapAddMonoidHom (fun j => (parent j,j))) _ _]
  exact Finset.sum_congr rfl (fun i _ => links_eq_map_labels U S parent h i)

end Parent
end BoundedBranch

 

open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter

namespace SKQAOA.Locality
variable {n : ℕ}

def ball (E : Finset (Edge n)) (S : Finset (Fin n)) : ℕ → Finset (Fin n)
  | 0 => S
  | h+1 => neighborhood E (ball E S h)

lemma ball_mono (E : Finset (Edge n)) (S : Finset (Fin n)) : Monotone (ball E S) := by
  apply monotone_nat_of_le_succ
  intro h
  exact subset_neighborhood E (ball E S h)

lemma subset_ball (E : Finset (Edge n)) (S : Finset (Fin n)) (h : ℕ) : S⊆ball E S h :=
  ball_mono E S (Nat.zero_le h)

lemma ball_succ_start (E : Finset (Edge n)) (S : Finset (Fin n)) (h : ℕ) :
    ball E (neighborhood E S) h=ball E S (h+1) := by
  induction h with
  | zero => rfl
  | succ h ih => exact congrArg (neighborhood E) ih

lemma incident_mem_neighborhood {E : Finset (Edge n)} {S : Finset (Fin n)} {e : Edge n}
    (he : e∈E) (hu : e.1.1∈S ∨ e.1.2∈S) :
    e.1.1∈neighborhood E S ∧ e.1.2∈neighborhood E S :=
  active_endpoints (Finset.mem_filter.mpr ⟨he,hu⟩)

 
lemma new_vertex_parent {E : Finset (Edge n)} {S : Finset (Fin n)} {v : Fin n}
    (hv : v∈neighborhood E S) (hvS : v∉S) :
    ∃(u : Fin n) (e : Edge n), e∈E ∧ u∈S ∧
      ((e.1.1=v ∧ e.1.2=u) ∨ (e.1.1=u ∧ e.1.2=v)) := by
  rcases Finset.mem_union.mp hv with hv | hv
  · exact (hvS hv).elim
  rcases Finset.mem_biUnion.mp hv with ⟨e,he,hve⟩
  rcases Finset.mem_filter.mp he with ⟨he,htouch⟩
  rcases Finset.mem_insert.mp hve with hve | hve
  · have hv' : e.1.1=v := hve.symm
    have hu : e.1.2∈S := by
      rcases htouch with h|h
      · exact (hvS (hv' ▸ h)).elim
      · exact h
    exact ⟨e.1.2,e,he,hu,Or.inl ⟨hv',rfl⟩⟩
  · have hv' : e.1.2=v := (Finset.mem_singleton.mp hve).symm
    have hu : e.1.1∈S := by
      rcases htouch with h|h
      · exact h
      · exact (hvS (hv' ▸ h)).elim
    exact ⟨e.1.1,e,he,hu,Or.inr ⟨rfl,hv'⟩⟩

 
def rank (E : Finset (Edge n)) (S : Finset (Fin n)) (v : Fin n) : ℕ :=
  sInf {h | v∈ball E S h}

lemma rank_le_of_mem {E : Finset (Edge n)} {S : Finset (Fin n)} {v : Fin n} {h : ℕ}
    (hv : v∈ball E S h) : rank E S v≤h := Nat.sInf_le hv

lemma mem_ball_rank {E : Finset (Edge n)} {S : Finset (Fin n)} {v : Fin n} {h : ℕ}
    (hv : v∈ball E S h) : v∈ball E S (rank E S v) :=
  Nat.sInf_mem (show Set.Nonempty {k | v∈ball E S k} from ⟨h,hv⟩)

lemma rank_zero_iff {E : Finset (Edge n)} {S : Finset (Fin n)} {v : Fin n} {h : ℕ}
    (hv : v∈ball E S h) : rank E S v=0 ↔ v∈S := by
  constructor
  · intro hr
    have hh := mem_ball_rank hv
    rw [hr] at hh
    exact hh
  · intro hvS
    exact Nat.eq_zero_of_le_zero (rank_le_of_mem (h := 0) hvS)

 

theorem exists_parent {E : Finset (Edge n)} {S : Finset (Fin n)} {v : Fin n} {h : ℕ}
    (hv : v∈ball E S h) (hvS : v∉S) :
    ∃(u : Fin n) (e : Edge n), e∈E ∧ u∈ball E S h ∧
      rank E S u+1=rank E S v ∧
        ((e.1.1=v ∧ e.1.2=u) ∨ (e.1.1=u ∧ e.1.2=v)) := by
  have hr : rank E S v≠0 := fun hr => hvS ((rank_zero_iff hv).mp hr)
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hr
  have hvk : v∈neighborhood E (ball E S k) := by
    have hh := mem_ball_rank hv
    simpa only [hk,ball] using hh
  have hvnot : v∉ball E S k := by
    intro hh
    have := rank_le_of_mem hh
    omega
  obtain ⟨u,e,he,hu,hend⟩ := new_vertex_parent hvk hvnot
  have huk : rank E S u≤k := rank_le_of_mem hu
  have hub : u∈ball E S (rank E S u) := mem_ball_rank hu
  have hvup : v∈ball E S (rank E S u+1) := by
    have ht : e.1.1∈ball E S (rank E S u) ∨ e.1.2∈ball E S (rank E S u) := by
      rcases hend with ⟨_,he₂⟩|⟨he₁,_⟩
      · exact Or.inr (he₂ ▸ hub)
      · exact Or.inl (he₁ ▸ hub)
    have ha := incident_mem_neighborhood he ht
    rcases hend with ⟨he₁,_⟩|⟨_,he₂⟩
    · exact he₁ ▸ ha.1
    · exact he₂ ▸ ha.2
  have hvr := rank_le_of_mem hvup
  have hbound := rank_le_of_mem hv
  refine ⟨u,e,he,ball_mono E S (by omega) hu,by omega,hend⟩

 

theorem relevant_endpoints_in_ball (E : Finset (Edge n)) (p : ℕ)
    (γ β : Fin p → ℝ) (S : Finset (Fin n)) {e : Edge n}
    (he : e∈relevantEdges E (qaoaWord p γ β) S) :
    e.1.1∈ball E S p ∧ e.1.2∈ball E S p := by
  induction p generalizing S with
  | zero => simp [qaoaWord,relevantEdges] at he
  | succ p ih =>
    simp only [qaoaWord,relevantEdges] at he
    rcases Finset.mem_union.mp he with he|he
    · have hh := active_endpoints he
      exact ⟨ball_mono E S (by omega : 1≤p+1) hh.1,
        ball_mono E S (by omega : 1≤p+1) hh.2⟩
    · have hh := ih _ _ _ he
      simpa only [ball_succ_start] using hh

end Locality

namespace SiteHistories
variable {n : ℕ}

lemma ball_subset_used (r : Edge n) (H : Finset (Edge n)) (p : ℕ) :
    Locality.ball (H∪{r}) {r.1.1,r.1.2} p ⊆ usedVertices r H := by
  induction p with
  | zero =>
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl|hv
    · exact fst_mem_usedVertices _ _ (by simp)
    · have := Finset.mem_singleton.mp hv
      subst v
      exact snd_mem_usedVertices _ _ (by simp)
  | succ p ih =>
    intro v hv
    rcases Finset.mem_union.mp hv with hv|hv
    · exact ih hv
    rcases Finset.mem_biUnion.mp hv with ⟨e,he,hv⟩
    exact Finset.mem_biUnion.mpr ⟨e,(Finset.mem_filter.mp he).1,hv⟩

 

theorem used_eq_ball (p : ℕ) (γ β : Fin p → ℝ) (r : Edge n)
    (H : Finset (Edge n))
    (hcone : H⊆Locality.relevantEdges (H∪{r}) (qaoaWord p γ β) {r.1.1,r.1.2}) :
    usedVertices r H=Locality.ball (H∪{r}) {r.1.1,r.1.2} p := by
  apply Finset.Subset.antisymm _ (ball_subset_used r H p)
  intro v hv
  rcases Finset.mem_biUnion.mp hv with ⟨e,he,hv⟩
  rcases Finset.mem_union.mp he with he|he
  · have hh := Locality.relevant_endpoints_in_ball (H∪{r}) p γ β _ (hcone he)
    rcases Finset.mem_insert.mp hv with hv|hv
    · exact hv ▸ hh.1
    · exact (Finset.mem_singleton.mp hv) ▸ hh.2
  · have he' := Finset.mem_singleton.mp he
    subst e
    exact Locality.subset_ball _ _ p hv

end SiteHistories
end SKQAOA

 

open scoped BigOperators

namespace SKQAOA
namespace FiniteGraph
variable {n : ℕ}

 

def pairEdges (u v : Fin n) : Finset (Edge n) :=
  if h : u<v then {⟨(u,v),h⟩} else
    if h' : v<u then {⟨(v,u),h'⟩} else ∅

lemma mem_pairEdges (u v : Fin n) (e : Edge n) :
    e∈pairEdges u v ↔ ((e.1.1=u ∧ e.1.2=v) ∨ (e.1.1=v ∧ e.1.2=u)) := by
  simp only [pairEdges]
  split_ifs with h h'
  · rw [Finset.mem_singleton]
    constructor
    · rintro rfl
      exact Or.inl ⟨rfl,rfl⟩
    · rintro (⟨hu,hv⟩|⟨hv,hu⟩)
      · exact Subtype.ext (Prod.ext hu hv)
      · have := e.2
        rw [hu,hv] at this
        exact (lt_asymm h this).elim
  · rw [Finset.mem_singleton]
    constructor
    · rintro rfl
      exact Or.inr ⟨rfl,rfl⟩
    · rintro (⟨hu,hv⟩|⟨hv,hu⟩)
      · have := e.2
        rw [hu,hv] at this
        exact (h this).elim
      · exact Subtype.ext (Prod.ext hv hu)
  · simp only [Finset.notMem_empty,false_iff]
    rintro (⟨hu,hv⟩|⟨hv,hu⟩)
    · exact h (by simpa only [hu,hv] using e.2)
    · exact h' (by simpa only [hu,hv] using e.2)

def edgesOfLinks (l : Multiset (Fin n × Fin n)) : Finset (Edge n) :=
  l.toFinset.biUnion (fun q => pairEdges q.1 q.2)

lemma mem_edgesOfLinks (l : Multiset (Fin n × Fin n)) (e : Edge n) :
    e∈edgesOfLinks l ↔ ∃q∈l,
      ((e.1.1=q.1 ∧ e.1.2=q.2) ∨ (e.1.1=q.2 ∧ e.1.2=q.1)) := by
  simp only [edgesOfLinks,Finset.mem_biUnion,Multiset.mem_toFinset,mem_pairEdges]

 

lemma parentEdge_injective (U S : Finset (Fin n)) (parent : Fin n → Fin n)
    (rank : Fin n → ℕ) (edge : Fin n → Edge n)
    (hrank : ∀j∈U\S, rank (parent j)+1=rank j)
    (hedge : ∀j∈U\S, (edge j∈pairEdges (parent j) j)) :
    Set.InjOn edge (↑(U\S) : Set (Fin n)) := by
  intro i hi j hj heq
  have hi' := (mem_pairEdges (parent i) i (edge i)).mp (hedge i hi)
  have hj' := (mem_pairEdges (parent j) j (edge j)).mp (hedge j hj)
  rw [heq] at hi'
  rcases hi' with ⟨hp,hi'⟩|⟨hi',hp⟩ <;> rcases hj' with ⟨hq,hj'⟩|⟨hj',hq⟩
  · exact hi'.symm.trans hj'
  · have h1 : parent i=j := hp.symm.trans hj'
    have h2 : parent j=i := hq.symm.trans hi'
    have hir := hrank i hi
    have hjr := hrank j hj
    rw [h1] at hir
    rw [h2] at hjr
    omega
  · have h1 : parent i=j := hp.symm.trans hj'
    have h2 : parent j=i := hq.symm.trans hi'
    have hir := hrank i hi
    have hjr := hrank j hj
    rw [h1] at hir
    rw [h2] at hjr
    omega
  · exact hi'.symm.trans hj'

lemma edge_unique {u v : Fin n} {e f : Edge n}
    (he : e∈pairEdges u v) (hf : f∈pairEdges u v) : e=f := by
  unfold pairEdges at he hf
  split_ifs at he hf <;> simp_all

lemma edgesOfLinks_parent (U S : Finset (Fin n)) (parent : Fin n → Fin n)
    (edge : Fin n → Edge n)
    (hedge : ∀j∈U\S, edge j∈pairEdges (parent j) j) :
    edgesOfLinks ((U\S).val.map (fun j => (parent j,j)))=(U\S).image edge := by
  ext e
  simp only [mem_edgesOfLinks,Multiset.mem_map,Finset.mem_val,Finset.mem_image]
  constructor
  · rintro ⟨q,⟨j,hj,rfl⟩,he⟩
    exact ⟨j,hj,(edge_unique (hedge j hj) ((mem_pairEdges _ _ _).mpr he))⟩
  · rintro ⟨j,hj,rfl⟩
    exact ⟨(parent j,j),⟨j,hj,rfl⟩,(mem_pairEdges _ _ _).mp (hedge j hj)⟩

end FiniteGraph
end SKQAOA

 

open scoped BigOperators Topology

namespace BoundedBranch
abbrev Forest (n h : ℕ) := Tree n h × Tree n h

def forestSize {n h : ℕ} (b : Forest n h) : ℕ := size n h b.1+size n h b.2

def forestLabels {n h : ℕ} (b : Forest n h) : Multiset (Fin n) :=
  labels n h b.1+labels n h b.2

def forestLinks {n h : ℕ} (r₁ r₂ : Fin n) (b : Forest n h) : Multiset (Fin n × Fin n) :=
  links n h r₁ b.1+links n h r₂ b.2

def forestWeight {n h : ℕ} (x : ℝ) (b : Forest n h) : ℝ :=
  weight n x h b.1*weight n x h b.2

@[simp] lemma card_forestLabels {n h : ℕ} (b : Forest n h) :
    (forestLabels b).card=forestSize b := by simp [forestLabels,forestSize]

@[simp] lemma card_forestLinks {n h : ℕ} (r₁ r₂ : Fin n) (b : Forest n h) :
    (forestLinks r₁ r₂ b).card=forestSize b := by simp [forestLinks,forestSize]

@[simp] lemma map_snd_forestLinks {n h : ℕ} (r₁ r₂ : Fin n) (b : Forest n h) :
    (forestLinks r₁ r₂ b).map Prod.snd=forestLabels b := by
  simp only [forestLinks,Multiset.map_add,map_snd_links,forestLabels]

lemma forestWeight_eq_pow {n h : ℕ} (x : ℝ) (b : Forest n h) :
    forestWeight x b=(x/(n:ℝ))^(forestSize b) := by
  simp only [forestWeight,weight_eq_pow,forestSize,pow_add]

lemma forestWeight_nonneg {n h : ℕ} {x : ℝ} (hx : 0≤x) (b : Forest n h) :
    0≤forestWeight x b :=
  mul_nonneg (weight_nonneg n h hx b.1) (weight_nonneg n h hx b.2)

lemma forestWeight_scale {n h : ℕ} (x z : ℝ) (b : Forest n h) :
    forestWeight (z*x) b=z^(forestSize b)*forestWeight x b := by
  simp only [forestWeight_eq_pow,mul_div_assoc,mul_pow]

lemma sum_forestWeight (n h : ℕ) (x : ℝ) :
    (∑b : Forest n h,forestWeight x b)=(partition n h x)^2 := by
  simp only [forestWeight,Fintype.sum_prod_type,←Finset.mul_sum,←Finset.sum_mul,
    partition,pow_two]

lemma sum_forestWeight_le_tower (n h : ℕ) {x : ℝ} (hx : 0≤x) :
    (∑b : Forest n h,forestWeight x b)≤(tower x h)^2 := by
  rw [sum_forestWeight]
  exact pow_le_pow_left₀ (partition_nonneg n h hx) (partition_le_tower n h hx) 2

 
lemma forest_tail_bound (n h L : ℕ) {x : ℝ} (hx : 0≤x) :
    (∑b : Forest n h with L≤forestSize b,forestWeight x b)≤(tower (2*x) h)^2/(2:ℝ)^L := by
  have hp : (0:ℝ)<2^L := pow_pos (by norm_num) _
  apply (le_div_iff₀ hp).mpr
  rw [mul_comm,Finset.mul_sum]
  calc
    _ ≤ ∑b : Forest n h with L≤forestSize b,forestWeight (2*x) b := by
      apply Finset.sum_le_sum
      intro b hb
      rw [forestWeight_scale]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (Finset.mem_filter.mp hb).2)
        (forestWeight_nonneg hx b)
    _ ≤ ∑b : Forest n h,forestWeight (2*x) b :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun b _ _ => forestWeight_nonneg (by positivity) b)
    _ ≤ _ := sum_forestWeight_le_tower n h (by positivity)

end BoundedBranch

 

open scoped BigOperators

namespace SKQAOA.SiteHistories
open BoundedBranch Locality FiniteGraph
variable {n : ℕ}

def roots (r : Edge n) : Finset (Fin n) := {r.1.1,r.1.2}
def reached (r : Edge n) (H : Finset (Edge n)) (p : ℕ) : Finset (Fin n) :=
  ball (H∪{r}) (roots r) p

def distance (r : Edge n) (H : Finset (Edge n)) : Fin n → ℕ :=
  rank (H∪{r}) (roots r)

lemma exists_parent_pair (r : Edge n) (H : Finset (Edge n)) (p : ℕ) (v : Fin n)
    (hv : v∈reached r H p\roots r) :
    ∃q : Fin n × Edge n, q.2∈H∪{r} ∧ q.1∈reached r H p ∧
      distance r H q.1+1=distance r H v ∧ q.2∈pairEdges q.1 v := by
  obtain ⟨u,e,he,hu,hr,hend⟩ := exists_parent (Finset.mem_sdiff.mp hv).1
    (Finset.mem_sdiff.mp hv).2
  refine ⟨(u,e),he,hu,hr,(mem_pairEdges _ _ _).mpr ?_⟩
  exact hend.symm

def parentPair (r : Edge n) (H : Finset (Edge n)) (p : ℕ) (v : Fin n) : Fin n × Edge n :=
  if hv : v∈reached r H p\roots r then
    Classical.choose (exists_parent_pair r H p v hv) else (v,r)

lemma parentPair_spec (r : Edge n) (H : Finset (Edge n)) (p : ℕ) (v : Fin n)
    (hv : v∈reached r H p\roots r) :
    (parentPair r H p v).2∈H∪{r} ∧ (parentPair r H p v).1∈reached r H p ∧
      distance r H (parentPair r H p v).1+1=distance r H v ∧
        (parentPair r H p v).2∈pairEdges (parentPair r H p v).1 v := by
  simpa only [parentPair,dite_eq_left hv] using Classical.choose_spec (exists_parent_pair r H p v hv)

def parent (r : Edge n) (H : Finset (Edge n)) (p : ℕ) (v : Fin n) : Fin n :=
  (parentPair r H p v).1

def parentEdge (r : Edge n) (H : Finset (Edge n)) (p : ℕ) (v : Fin n) : Edge n :=
  (parentPair r H p v).2

lemma parent_spec (r : Edge n) (H : Finset (Edge n)) (p : ℕ) :
    ∀v∈reached r H p\roots r, parent r H p v∈reached r H p ∧
      distance r H (parent r H p v)+1=distance r H v := by
  intro v hv
  exact ⟨(parentPair_spec r H p v hv).2.1,(parentPair_spec r H p v hv).2.2.1⟩

lemma distance_zero (r : Edge n) (H : Finset (Edge n)) (p : ℕ) :
    ∀v∈reached r H p, distance r H v=0 ↔ v∈roots r := by
  intro v hv
  exact rank_zero_iff hv

lemma distance_bound (r : Edge n) (H : Finset (Edge n)) (p : ℕ) :
    ∀v∈reached r H p, distance r H v≤p := by
  intro v hv
  exact rank_le_of_mem hv

lemma roots_subset_reached (r : Edge n) (H : Finset (Edge n)) (p : ℕ) :
    roots r⊆reached r H p := subset_ball _ _ _

lemma parentEdge_mem (r : Edge n) (H : Finset (Edge n)) (p : ℕ) (v : Fin n)
    (hv : v∈reached r H p\roots r) : parentEdge r H p v∈H := by
  have hh := parentPair_spec r H p v hv
  rcases Finset.mem_union.mp hh.1 with he|he
  · exact he
  · have he' : parentEdge r H p v=r := Finset.mem_singleton.mp he
    have hvnot := (Finset.mem_sdiff.mp hv).2
    have hl : parentEdge r H p v∈pairEdges (parent r H p v) v := hh.2.2.2
    rw [he'] at hl
    rcases (mem_pairEdges _ _ _).mp hl with ⟨_,hrv⟩|⟨hrv,_⟩
    · exact (hvnot (by simp [roots,←hrv])).elim
    · exact (hvnot (by simp [roots,←hrv])).elim

 

def forestCode (r : Edge n) (H : Finset (Edge n)) (p : ℕ) : Forest n p :=
  (unfoldTree (reached r H p) (roots r) (parent r H p) p r.1.1,
   unfoldTree (reached r H p) (roots r) (parent r H p) p r.1.2)

lemma forestCode_labels (r : Edge n) (H : Finset (Edge n)) (p : ℕ) :
    forestLabels (forestCode r H p)=(reached r H p\roots r).val := by
  have he := Parent.sum_labels_roots (reached r H p) (roots r) (parent r H p)
    (distance r H) (roots_subset_reached r H p)
    (distance_zero r H p) (parent_spec r H p) p (distance_bound r H p)
  simpa only [roots,Finset.sum_pair (ne_of_lt r.2),forestLabels,forestCode] using he

lemma forestCode_links (r : Edge n) (H : Finset (Edge n)) (p : ℕ) :
    forestLinks r.1.1 r.1.2 (forestCode r H p)=
      (reached r H p\roots r).val.map (fun v => (parent r H p v,v)) := by
  have he := Parent.sum_links_roots (reached r H p) (roots r) (parent r H p)
    (distance r H) (roots_subset_reached r H p)
    (distance_zero r H p) (parent_spec r H p) p (distance_bound r H p)
  simpa only [roots,Finset.sum_pair (ne_of_lt r.2),forestLinks,forestCode] using he

lemma forestCode_size (r : Edge n) (H : Finset (Edge n)) (p : ℕ) :
    forestSize (forestCode r H p)=(reached r H p\roots r).card := by
  rw [←card_forestLabels,forestCode_labels]
  rfl

def forestVertices {p : ℕ} (r : Edge n) (b : Forest n p) : Finset (Fin n) :=
  roots r∪(forestLabels b).toFinset

def forestEdges {p : ℕ} (r : Edge n) (b : Forest n p) : Finset (Edge n) :=
  edgesOfLinks (forestLinks r.1.1 r.1.2 b)

lemma forestCode_vertices (r : Edge n) (H : Finset (Edge n)) (p : ℕ) :
    forestVertices r (forestCode r H p)=reached r H p := by
  rw [forestVertices,forestCode_labels]
  simp only [Finset.val_toFinset]
  exact Finset.union_sdiff_of_subset (roots_subset_reached r H p)

lemma forestCode_edges (r : Edge n) (H : Finset (Edge n)) (p : ℕ) :
    forestEdges r (forestCode r H p)=(reached r H p\roots r).image (parentEdge r H p) := by
  rw [forestEdges,forestCode_links]
  exact edgesOfLinks_parent _ _ _ _ (fun v hv => (parentPair_spec r H p v hv).2.2.2)

lemma forestCode_edges_subset (r : Edge n) (H : Finset (Edge n)) (p : ℕ) :
    forestEdges r (forestCode r H p)⊆H := by
  rw [forestCode_edges]
  rintro e he
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp he
  exact parentEdge_mem r H p v hv

lemma forestCode_edges_card (r : Edge n) (H : Finset (Edge n)) (p : ℕ) :
    (forestEdges r (forestCode r H p)).card=forestSize (forestCode r H p) := by
  rw [forestCode_edges,forestCode_size]
  apply Finset.card_image_iff.mpr
  exact parentEdge_injective _ _ _ (distance r H) _
    (fun v hv => (parent_spec r H p v hv).2)
    (fun v hv => (parentPair_spec r H p v hv).2.2.2)

end SKQAOA.SiteHistories

end

end OAI
