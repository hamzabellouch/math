import OAI.Combinatorics.Ramsey.CycleClique.Construction.PathRotation
import OAI.Combinatorics.Ramsey.CycleClique.Construction.DenseSubgraph

namespace OAI

/-!
# Possible endpoints on a fixed path vertex set

These are the endpoint-clique and rotation consequences in manuscript
Lemma `clq:coloured-path`.
-/

namespace CycleClique.Construction
def IsSpanningPath {V : Type*} (G : SimpleGraph V) (x : V) (W : Finset V)
    {r : ℕ} (f : Fin (r + 1) → V) : Prop :=
  Function.Injective f ∧
    (∀ i : Fin r, G.Adj (f i.castSucc) (f i.succ)) ∧
    f 0 = x ∧ Set.range f = (W : Set V)

noncomputable def pathEnds {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x : V) (W : Finset V) (r : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun e => ∃ f : Fin (r + 1) → V,
    IsSpanningPath G x W f ∧ f (Fin.last r) = e

@[simp] theorem mem_pathEnds {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x e : V} {W : Finset V} {r : ℕ} :
    e ∈ pathEnds G x W r ↔ ∃ f : Fin (r + 1) → V,
      IsSpanningPath G x W f ∧ f (Fin.last r) = e := by
  classical
  simp [pathEnds]

theorem pathEnds_subset {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x : V) (W : Finset V) (r : ℕ) : pathEnds G x W r ⊆ W := by
  intro e he
  obtain ⟨f, hf, rfl⟩ := mem_pathEnds.mp he
  change f (Fin.last r) ∈ (W : Set V)
  rw [← hf.2.2.2]
  exact ⟨Fin.last r, rfl⟩

theorem start_not_pathEnds {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x : V} {W : Finset V} {r : ℕ} (hr : 1 ≤ r) :
    x ∉ pathEnds G x W r := by
  intro hx
  obtain ⟨f, hf, heq⟩ := mem_pathEnds.mp hx
  have hi := congrArg Fin.val (hf.1 (hf.2.2.1.trans heq.symm))
  simp only [Fin.val_zero, Fin.val_last] at hi
  omega

/-- The successor of any neighbour of the last vertex becomes an
endpoint by the explicit fixed-end rotation. -/
theorem successor_mem_pathEnds {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x : V} {W : Finset V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsSpanningPath G x W f)
    (i : Fin r) (hi : G.Adj (f (Fin.last r)) (f i.castSucc)) :
    f i.succ ∈ pathEnds G x W r := by
  have hrot := rotate_path f hf.1 hf.2.1 i hi
  exact mem_pathEnds.mpr ⟨f ∘ rotationIndex i,
    ⟨hrot.1, hrot.2.1, hrot.2.2.1.trans hf.2.2.1,
      hrot.2.2.2.2.trans hf.2.2.2⟩, hrot.2.2.2.1⟩

/-- Independent-pair expansion makes a set of possible endpoints a
clique when their neighbourhoods fit inside too few vertices. -/
theorem clique_of_endpoint_neighbor_cover {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {E W Z : Finset V} {s : ℕ}
    (hEW : E ⊆ W)
    (hcover : ∀ e ∈ E, ∀ v, G.Adj e v → v ∈ W ∪ Z)
    (hsize : W.card + Z.card < 2 * s)
    (hexpand : ∀ a b, a ≠ b → ¬ G.Adj a b →
      2 * s ≤ (closedNeighborhood G {a, b}).card) : G.IsClique (E : Set V) := by
  classical
  intro a ha b hb hab
  by_contra hn
  have hsub : closedNeighborhood G {a, b} ⊆ W ∪ Z := by
    intro v hv
    rcases mem_closedNeighborhood.mp hv with hv | ⟨e, he, hev⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact Finset.mem_union_left _ (hEW ha)
      · exact Finset.mem_union_left _ (hEW hb)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact hcover _ ha v hev
      · exact hcover _ hb v hev
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le W Z)
  have hlow := hexpand a b hab hn
  omega

/-- Each neighbour of an endpoint has a different successor endpoint,
so its degree is at most the number of possible endpoints. -/
theorem endpoint_degree_le {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x e : V} {W : Finset V} {r : ℕ}
    (he : e ∈ pathEnds G x W r)
    (hneighbors : ∀ v, G.Adj e v → v ∈ W) :
    (G.neighborSet e).ncard ≤ (pathEnds G x W r).card := by
  classical
  obtain ⟨f, hf, hlast⟩ := mem_pathEnds.mp he
  have hex : ∀ v : G.neighborFinset e, ∃ i : Fin r, f i.castSucc = v.val := by
    intro v
    have hadj := (G.mem_neighborFinset e v.val).mp v.property
    have hv : v.val ∈ Set.range f := by
      rw [hf.2.2.2]
      exact hneighbors v.val hadj
    obtain ⟨j, hj⟩ := hv
    have hjlt : j.val < r := by
      have hneq : j ≠ Fin.last r := by
        intro heq
        subst j
        have heq' : e = v.val := hlast.symm.trans hj
        exact hadj.ne heq'
      have hval : j.val ≠ r := fun h => hneq (Fin.ext h)
      omega
    exact ⟨⟨j.val, hjlt⟩, by simpa using hj⟩
  let pivot : G.neighborFinset e → Fin r := fun v => Classical.choose (hex v)
  have hpivot : ∀ v : G.neighborFinset e, f (pivot v).castSucc = v.val :=
    fun v => Classical.choose_spec (hex v)
  let suc : G.neighborFinset e → pathEnds G x W r := fun v =>
    ⟨f (pivot v).succ, successor_mem_pathEnds hf (pivot v) (by
      rw [hlast, hpivot]
      exact (G.mem_neighborFinset e v.val).mp v.property)⟩
  have hinj : Function.Injective suc := by
    intro a b hab
    have hfin := hf.1 (congrArg Subtype.val hab)
    have hp : pivot a = pivot b := Fin.succ_injective r hfin
    apply Subtype.ext
    rw [← hpivot a, ← hpivot b, hp]
  have hcard := Fintype.card_le_of_injective suc hinj
  simpa only [Fintype.card_coe, SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.ncard_neighborSet] using hcard

/-- On any spanning path the endpoint clique is a final segment. -/
theorem pathEnds_successor_closed {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x : V} {W : Finset V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsSpanningPath G x W f)
    (hclique : G.IsClique (pathEnds G x W r : Set V))
    {i : Fin r} (hi : f i.castSucc ∈ pathEnds G x W r) :
    f i.succ ∈ pathEnds G x W r := by
  apply successor_mem_pathEnds hf
  have he : f (Fin.last r) ∈ pathEnds G x W r := mem_pathEnds.mpr ⟨f, hf, rfl⟩
  apply hclique he hi
  intro heq
  have := congrArg Fin.val (hf.1 heq)
  simp only [Fin.val_last, Fin.val_castSucc] at this
  omega

end CycleClique.Construction

end OAI
