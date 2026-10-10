import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.BinarySwitches

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph LazyDFS BinaryInterpolation InterpolationForest

variable {V E : Type*} (G : BondGraph V E)

def HasSide (L : List (V × Bool)) (ω : Set E) (b : Bool) (v : V) : Prop :=
  ∃ z ∈ L, z.2=b ∧ (G.openGraph ω).Reachable z.1 v

lemma hasSide_mono_reachable (L : List (V × Bool)) (ω : Set E) (b : Bool) {u v : V}
    (hu : HasSide G L ω b u) (hr : (G.openGraph ω).Reachable u v) :
    HasSide G L ω b v := by
  obtain ⟨z,hz,hb,hrz⟩ := hu
  exact ⟨z,hz,hb,hrz.trans hr⟩

lemma hasSide_unique (L : List (V × Bool)) (ω : Set E) (hL : Consistent G L ω)
    {b c : Bool} {v : V} (hb : HasSide G L ω b v) (hc : HasSide G L ω c v) : b=c := by
  obtain ⟨z,hz,hzb,hzv⟩ := hb
  obtain ⟨t,ht,htc,htv⟩ := hc
  exact hzb.symm.trans ((hL z hz t ht (hzv.trans htv.symm)).trans htc)

section Output
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma switched_side_adj (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (hL : Consistent G (anchors d x n h) ω)
    (S : Finset ℕ) (hS : ∀ i ∈ S, 2 ≤ i ∧ i < n+2) {b : Bool} {u v : V}
    (hu : HasSide G (anchors d x n h) ω b u)
    (huv : (G.openGraph (switched n h ω S)).Adj u v) :
    HasSide G (anchors d x n h) ω b v := by
  obtain ⟨⟨e,he,hev⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huv
  rcases he with he|⟨i,hi,him⟩
  · exact hasSide_mono_reachable G _ ω b hu (prop_openEdge_reachable G ω he hev)
  · obtain ⟨_,a,c,heac,ha,hc⟩ := node_mark_geometry G order d x p w r₀ n h ω hr i
      (hS i hi).1 (hS i hi).2 e him
    have hip := nodeParent_lt G d x ω n h i (hS i hi).1
    have hcol := node_colour_parent G order d x p w r₀ n h ω hr i (hS i hi).1 (hS i hi).2
    have hA : HasSide G (anchors d x n h) ω (node d x n h i).2 a :=
      ⟨_,node_mem d x n h i (hS i hi).2,rfl,ha⟩
    have hC : HasSide G (anchors d x n h) ω (node d x n h i).2 c :=
      ⟨_,node_mem d x n h _ (hip.trans (hS i hi).2),hcol.symm,hc⟩
    rcases Sym2.eq_iff.mp (hev.symm.trans heac) with ⟨hua,hvc⟩|⟨huc,hva⟩
    · subst u; subst v
      exact (hasSide_unique G _ ω hL hu hA).symm ▸ hC
    · subst u; subst v
      exact (hasSide_unique G _ ω hL hu hC).symm ▸ hA

lemma switched_side_reachable (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (hL : Consistent G (anchors d x n h) ω)
    (S : Finset ℕ) (hS : ∀ i ∈ S, 2 ≤ i ∧ i < n+2) {b : Bool} {u v : V}
    (hu : HasSide G (anchors d x n h) ω b u)
    (huv : (G.openGraph (switched n h ω S)).Reachable u v) :
    HasSide G (anchors d x n h) ω b v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at huv
  induction huv with
  | refl => exact hu
  | tail _ hstep ih => exact switched_side_adj G order d x p w r₀ n h ω hr hL S hS ih hstep

theorem switched_terminal_distinct (s n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w (seed G w (x 0) (x d) s) n h ω ≠ 0)
    (S : Finset ℕ) (hS : ∀ i ∈ S, 2 ≤ i ∧ i < n+2) :
    ¬(G.openGraph (switched n h ω S)).Reachable
      (x (interval d n h).1) (x (interval d n h).2) := by
  intro hreach
  have hL := density_consistent G order d x p w s n h ω hr
  have he := endpoint_labels d x n h
  have hl : HasSide G (anchors d x n h) ω true (x (interval d n h).1) :=
    ⟨_,he.1,rfl,.refl _⟩
  have hr' : HasSide G (anchors d x n h) ω false (x (interval d n h).2) :=
    ⟨_,he.2,rfl,.refl _⟩
  have hh := switched_side_reachable G order d x p w _ n h ω hr hL S hS hl hreach
  cases hasSide_unique G _ ω hL hh hr'

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma active_index_bounds (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (ω : Set E) :
    ∀ i ∈ activeNodes G d x n h ω, 2 ≤ i ∧ i < n+2 := by
  intro i hi
  exact ⟨((historyForest G d x ω n h).mem_active.mp hi).2,active_lt G d x n h ω i hi⟩

lemma active_lineage_reachable (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (u : ℕ) (hu : u = owner G d x n h ω (x (interval d n h).1) ∨
      u = owner G d x n h ω (x (interval d n h).2))
    (i : ℕ) (hi : i ∈ (historyForest G d x ω n h).lineage u) (hin : i < n+2) :
    (G.openGraph (switched n h ω (activeNodes G d x n h ω))).Reachable
      (node d x n h i).1 (node d x n h ((historyForest G d x ω n h).root i)).1 := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases hib : i < 2
    · rw [Forest.root_base _ hib]
    · have hi2 : 2 ≤ i := by omega
      have hia : i ∈ activeNodes G d x n h ω := by
        apply (Forest.mem_active _).mpr
        exact ⟨hu.elim (fun e => Or.inl (e ▸ hi)) (fun e => Or.inr (e ▸ hi)),hi2⟩
      have hm := active_nonhold G order d x p w r₀ n h ω hr i hia
      obtain ⟨e,he⟩ := Option.ne_none_iff_exists'.mp hm
      obtain ⟨_,a,b,heab,ha,hb⟩ := node_mark_geometry G order d x p w r₀ n h ω hr i hi2 hin e he
      have hmon := G.openGraph_mono (switched_mono n h ω (activeNodes G d x n h ω))
      have heopen : switched n h ω (activeNodes G d x n h ω) e := Or.inr ⟨i,hia,he⟩
      have hparent := (ha.mono hmon).trans
        ((prop_openEdge_reachable G _ heopen heab).trans (hb.symm.mono hmon))
      rw [Forest.root_step _ hi2]
      exact hparent.trans (ih _ (nodeParent_lt G d x ω n h i hi2)
        ((historyForest G d x ω n h).parent_mem_lineage hi2 hi)
        ((nodeParent_lt G d x ω n h i hi2).trans hin))

theorem switched_terminal_bases (s n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w (seed G w (x 0) (x d) s) n h ω ≠ 0) :
    let η := switched n h ω (activeNodes G d x n h ω)
    (G.openGraph η).Reachable (x (interval d n h).1) (x 0) ∧
    (G.openGraph η).Reachable (x (interval d n h).2) (x d) := by
  have he := endpoint_labels d x n h
  have hrts := terminal_roots G order d x p w s n h ω hr
  have hb := node_bases d x n h
  have hmon := G.openGraph_mono (switched_mono n h ω (activeNodes G d x n h ω))
  constructor
  · have hanc := active_lineage_reachable G order d x p w _ n h ω hr _ (Or.inl rfl) _
      ((historyForest G d x ω n h).self_mem_lineage _) (owner_lt G d x n h ω _ ⟨true,he.1⟩)
    rw [hrts.1,hb.1] at hanc
    exact ((owner_reachable G d x n h ω _ ⟨true,he.1⟩).mono hmon).trans hanc
  · have hanc := active_lineage_reachable G order d x p w _ n h ω hr _ (Or.inr rfl) _
      ((historyForest G d x ω n h).self_mem_lineage _) (owner_lt G d x n h ω _ ⟨false,he.2⟩)
    rw [hrts.2,hb.2] at hanc
    exact ((owner_reachable G d x n h ω _ ⟨false,he.2⟩).mono hmon).trans hanc

lemma density_seed_support (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0) : r₀ ω ≠ 0 := by
  induction n with
  | zero => exact hr
  | succ n ih => exact ih h.1 (density_step_support G order d x p w r₀ n h ω hr).1

theorem switched_endpointEvent (s n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w (seed G w (x 0) (x d) s) n h ω ≠ 0) :
    endpointEvent G (x (interval d n h).1) (x (interval d n h).2) s
      (switched n h ω (activeNodes G d x n h ω)) := by
  have hseed := density_seed_support G order d x p w _ n h ω hr
  have ho : endpointEvent G (x 0) (x d) s ω := by
    by_contra ho
    simp only [seed,ite_eq_right ho,mul_zero] at hseed
    exact hseed rfl
  have hb := switched_terminal_bases G order d x p w s n h ω hr
  have hmon := G.openGraph_mono (switched_mono n h ω (activeNodes G d x n h ω))
  refine ⟨switched_terminal_distinct G order d x p w s n h ω hr _
    (active_index_bounds G d x n h ω),?_,?_⟩
  · apply ho.2.1.trans
    apply Finset.card_le_card
    intro v hv
    have hv' : (G.openGraph ω).Reachable (x 0) v := (Set.mem_toFinset (s := G.cluster ω (x 0)) (a := v)).mp hv
    exact (Set.mem_toFinset (s := G.cluster (switched n h ω (activeNodes G d x n h ω)) (x (interval d n h).1)) (a := v)).mpr (hb.1.trans (hv'.mono hmon))
  · apply ho.2.2.trans
    apply Finset.card_le_card
    intro v hv
    have hv' : (G.openGraph ω).Reachable (x d) v := (Set.mem_toFinset (s := G.cluster ω (x d)) (a := v)).mp hv
    exact (Set.mem_toFinset (s := G.cluster (switched n h ω (activeNodes G d x n h ω)) (x (interval d n h).2)) (a := v)).mpr (hb.2.trans (hv'.mono hmon))

end Output
end CriticalPercolation.BinaryLaw
end
end

end OAI
