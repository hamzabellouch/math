import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Tactic.Tauto

namespace OAI

/-!
# Paths and cycles in finite two-port graphs

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

/-! A finite configuration
with two ports of degree one and internal degrees zero or two has an isolated
boundary path; the remainder consists of cycles. This lemma does not identify the
transfer matrix with the physical path partition function. -/
open SimpleGraph
namespace CriticalHoneycomb.Transfer.PathComponents
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma ncard_neighbors (v : V) : (G.neighborSet v).ncard = G.degree v := by
  change Nat.card (G.neighborSet v) = _
  rw [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]

lemma ports_reachable {a b : V} (ha : G.degree a = 1)
    (other : ∀ v, v ≠ a → v ≠ b → Even (G.degree v)) : G.Reachable a b := by
  classical
  let S : Set V := {v | G.Reachable a v}
  let A : S := ⟨a, SimpleGraph.Reachable.rfl⟩
  have deg (v : S) : (G.induce S).degree v = G.degree v := by
    apply G.degree_induce_of_neighborSet_subset
    intro w hw
    exact v.property.trans hw.reachable
  have hA : Odd ((G.induce S).degree A) := by rw [deg, ha]; decide
  obtain ⟨v, hvA, hv⟩ := (G.induce S).exists_ne_odd_degree_of_exists_odd_degree A hA
  have hva : (v : V) ≠ a := by
    intro e
    apply hvA
    exact Subtype.ext e
  have hvb : (v : V) = b := by
    by_contra e
    have he := other v hva e
    rw [deg] at hv
    exact (Nat.not_even_iff_odd.mpr hv) he
  exact hvb ▸ v.property

lemma path_neighbor_eq {a b v : V} (hab : a ≠ b)
    (ha : G.degree a = 1) (hb : G.degree b = 1)
    (upper : ∀ v, G.degree v ≤ 2)
    (p : G.Walk a b) (hp : p.IsPath) (hv : v ∈ p.support) :
    p.toSubgraph.neighborSet v = G.neighborSet v := by
  classical
  apply Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset v)
  rw [ncard_neighbors]
  by_cases h : v = a
  · subst v
    rw [ha, hp.neighborSet_toSubgraph_startpoint (Walk.not_nil_of_ne hab)]
    simp
  by_cases h' : v = b
  · subst v
    rw [hb, hp.neighborSet_toSubgraph_endpoint (Walk.not_nil_of_ne hab)]
    simp
  obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp hv
  have hi0 : i ≠ 0 := by intro e; subst i; exact h (hi.symm.trans p.getVert_zero)
  have hil' : i < p.length := by
    apply lt_of_le_of_ne hil
    intro e
    subst i
    exact h' (hi.symm.trans p.getVert_length)
  rw [← hi, hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hil']
  exact upper _

lemma path_closed {a b v w : V} (hab : a ≠ b)
    (ha : G.degree a = 1) (hb : G.degree b = 1)
    (upper : ∀ v, G.degree v ≤ 2)
    (p : G.Walk a b) (hp : p.IsPath) (hv : v ∈ p.support) (hvw : G.Adj v w) :
    w ∈ p.support := by
  have hn : p.toSubgraph.Adj v w := by
    change w ∈ p.toSubgraph.neighborSet v
    rw [path_neighbor_eq G hab ha hb upper p hp hv]
    exact hvw
  exact p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert hn.symm)

lemma residual_isCycles {a b : V} (hab : a ≠ b)
    (ha : G.degree a = 1) (hb : G.degree b = 1)
    (other : ∀ v, v ≠ a → v ≠ b → G.degree v = 0 ∨ G.degree v = 2)
    (p : G.Walk a b) (hp : p.IsPath) :
    (G \ p.toSubgraph.spanningCoe).IsCycles := by
  classical
  have upper (v : V) : G.degree v ≤ 2 := by
    by_cases h : v = a
    · subst v; rw [ha]; decide
    by_cases h' : v = b
    · subst v; rw [hb]; decide
    rcases other v h h' with h | h <;> omega
  intro v hv
  have hvnot : v ∉ p.support := by
    intro hvp
    obtain ⟨w, hw⟩ := hv
    have h := path_neighbor_eq G hab ha hb upper p hp hvp
    simp only [SimpleGraph.mem_neighborSet, SimpleGraph.sdiff_adj,
      SimpleGraph.Subgraph.spanningCoe_adj] at hw
    apply hw.2
    change w ∈ p.toSubgraph.neighborSet v
    rw [h]
    exact hw.1
  have heq : (G \ p.toSubgraph.spanningCoe).neighborSet v = G.neighborSet v := by
    ext w
    simp only [SimpleGraph.mem_neighborSet, SimpleGraph.sdiff_adj,
      SimpleGraph.Subgraph.spanningCoe_adj]
    constructor
    · exact And.left
    · intro hw
      refine ⟨hw, ?_⟩
      intro hf
      exact hvnot (p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert hf))
  rw [heq, ncard_neighbors]
  have hva : v ≠ a := by intro e; subst v; exact hvnot p.start_mem_support
  have hvb : v ≠ b := by intro e; subst v; exact hvnot p.end_mem_support
  rcases other v hva hvb with h | h
  · rw [heq] at hv
    have hn := hv.ncard_pos (Set.toFinite _)
    rw [ncard_neighbors, h] at hn
    omega
  · exact h

/-- Every finite nonbranching two-port configuration is a path plus cycles. The
path has no edge to the residual cycle graph. -/
theorem path_and_cycles {a b : V} (hab : a ≠ b)
    (ha : G.degree a = 1) (hb : G.degree b = 1)
    (other : ∀ v, v ≠ a → v ≠ b → G.degree v = 0 ∨ G.degree v = 2) :
    ∃ p : G.Walk a b, p.IsPath ∧ (G \ p.toSubgraph.spanningCoe).IsCycles ∧
      ∀ v ∈ p.support, p.toSubgraph.neighborSet v = G.neighborSet v := by
  have upper (v : V) : G.degree v ≤ 2 := by
    by_cases h : v = a
    · subst v; rw [ha]; decide
    by_cases h' : v = b
    · subst v; rw [hb]; decide
    rcases other v h h' with h | h <;> omega
  have hr := ports_reachable G ha (fun v h h' => by
    rcases other v h h' with e | e <;> rw [e] <;> decide)
  obtain ⟨p, hp⟩ := hr.exists_isPath
  exact ⟨p, hp, residual_isCycles G hab ha hb other p hp,
    fun v hv => path_neighbor_eq G hab ha hb upper p hp hv⟩
end CriticalHoneycomb.Transfer.PathComponents

namespace CriticalHoneycomb.Transfer.FiniteConfigurations
open SimpleGraph
variable {α : Type*}

/-- The hard-wall two-port graph: the two exterior markers have only their
prescribed incident edge; internal adjacency remains unchanged. -/
def portRel (R : α → α → Prop) (a b : α) : (α ⊕ Bool) → (α ⊕ Bool) → Prop
  | .inl x, .inl y => R x y
  | .inr false, .inl y | .inl y, .inr false => y=a
  | .inr true, .inl y | .inl y, .inr true => y=b
  | .inr _, .inr _ => False

lemma chain_snoc_ports (R : α → α → Prop) (a b : α) (xs : List α) :
    (xs.map Sum.inl ++ [Sum.inr true]).IsChain (portRel R a b) ↔
      xs.IsChain R ∧ ∀ z ∈ xs.getLast?, z=b := by
  rw [List.isChain_append,List.isChain_map]
  simp [portRel,List.getLast?_map]

lemma chain_ports (R : α → α → Prop) (a b : α) (xs : List α) :
    (Sum.inr false :: (xs.map Sum.inl ++ [Sum.inr true])).IsChain (portRel R a b) ↔
      xs.IsChain R ∧ xs.head?=some a ∧ xs.getLast?=some b := by
  cases xs with
  | nil => simp [portRel]
  | cons x xs =>
    rw [List.isChain_cons,chain_snoc_ports]
    have hh : (∀ y ∈ ((x::xs).map Sum.inl ++ [Sum.inr true]).head?,
        portRel R a b (.inr false) y) ↔ x=a := by
      simp [portRel]
    have hl : (∀ z ∈ (x::xs).getLast?, z=b) ↔ (x::xs).getLast?=some b := by
      rw [List.getLast?_eq_some_getLast (by simp)]
      simp
    rw [hh,hl]
    simp only [List.head?_cons,Option.some.injEq]
    tauto

lemma list_all_inl (l : List (α ⊕ Bool))
    (h : ∀ t ∈ l, ∀ b : Bool, t ≠ Sum.inr b) :
    ∃ xs : List α, xs.map Sum.inl=l := by
  induction l with
  | nil => exact ⟨[],rfl⟩
  | cons t l ih =>
    cases t with
    | inr b => exact (h _ (by simp) b rfl).elim
    | inl x =>
      obtain ⟨xs,hxs⟩ := ih (by aesop)
      exact ⟨x::xs,by simp [hxs]⟩

lemma support_decomposition {G : SimpleGraph (α ⊕ Bool)}
    (p : G.Walk (.inr false) (.inr true)) (hp : p.IsPath) :
    ∃ xs : List α, p.support = Sum.inr false :: (xs.map Sum.inl ++ [Sum.inr true]) ∧ xs.Nodup := by
  have hs := p.cons_tail_support.symm
  have hn := hp.support_nodup
  rw [hs] at hn
  obtain ⟨hna,hnt⟩ := List.nodup_cons.mp hn
  have ht : p.support.tail.getLast? = some (.inr true) := by
    have hl : p.support.getLast? = some (.inr true) := by
      rw [List.getLast?_eq_some_getLast (by simp),p.getLast_support]
    cases h : p.support.tail with
    | nil =>
      have he := congrArg List.getLast? hs
      simp [h,hl] at he
    | cons t ts =>
      have he := congrArg List.getLast? hs
      simpa [h,hl] using he.symm
  obtain ⟨mid,hmid⟩ := List.getLast?_eq_some_iff.mp ht
  rw [hmid] at hna hnt
  obtain ⟨hnm,_,hd⟩ := List.nodup_append.mp hnt
  obtain ⟨xs,hxs⟩ := list_all_inl mid (by
    intro t ht b he
    cases b
    · subst t
      exact hna (by simp [ht])
    · exact hd t ht (.inr true) (by simp) he)
  refine ⟨xs,?_,?_⟩
  · simpa [hmid,←hxs] using hs
  · exact List.Nodup.of_map Sum.inl (hxs.symm ▸ hnm)

end CriticalHoneycomb.Transfer.FiniteConfigurations


end OAI
