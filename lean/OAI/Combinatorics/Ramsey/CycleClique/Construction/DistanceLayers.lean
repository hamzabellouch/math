import OAI.Combinatorics.Ramsey.CycleClique.Construction.LayerSelection
import OAI.Combinatorics.Ramsey.CycleClique.Construction.IndependentPacking
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace OAI

/-!
# Distance layers and independent parity unions

Distance layers are restricted to the root's connected component.
Vertices in different layers of the same parity are anticomplete, so
maximum independent sets chosen there can be combined.
-/

namespace CycleClique.Construction
noncomputable def independentOn {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset V) : Finset V := by
  classical
  exact (Classical.choose (G.induce (D : Set V)).exists_isNIndepSet_indepNum).map
    ⟨Subtype.val, Subtype.val_injective⟩

theorem independentOn_subset {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset V) : independentOn G D ⊆ D := by
  classical
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
  exact i.property

theorem independentOn_independent {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset V) : G.IsIndepSet (independentOn G D : Set V) := by
  classical
  intro x hx y hy hxy h
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
  exact (Classical.choose_spec (G.induce (D : Set V)).exists_isNIndepSet_indepNum).isIndepSet
    hi hj (fun h => hxy (congrArg Subtype.val h)) h

theorem independentOn_card {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset V) :
    (independentOn G D).card = (G.induce (D : Set V)).indepNum := by
  classical
  rw [independentOn, Finset.card_map]
  exact (Classical.choose_spec (G.induce (D : Set V)).exists_isNIndepSet_indepNum).card_eq

/-- The exact-distance layer within the root component. -/
noncomputable def distanceLayer {V : Type*} [Fintype V]
    (G : SimpleGraph V) (root : V) (j : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => G.Reachable root v ∧ G.dist root v = j

@[simp] theorem mem_distanceLayer {V : Type*} [Fintype V]
    {G : SimpleGraph V} {root v : V} {j : ℕ} :
    v ∈ distanceLayer G root j ↔ G.Reachable root v ∧ G.dist root v = j := by
  classical
  simp [distanceLayer]

theorem distanceLayer_zero {V : Type*} [Fintype V] (G : SimpleGraph V) (root : V) :
    distanceLayer G root 0 = {root} := by
  classical
  ext v
  simp only [mem_distanceLayer, Finset.mem_singleton]
  constructor
  · rintro ⟨hr, hd⟩
    rcases G.dist_eq_zero_iff_eq_or_not_reachable.mp hd with h | h
    · exact h.symm
    · exact False.elim (h hr)
  · rintro rfl
    simp

theorem distanceLayers_disjoint {V : Type*} [Fintype V]
    (G : SimpleGraph V) (root : V) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (distanceLayer G root i) (distanceLayer G root j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hi
  exact hij ((mem_distanceLayer.mp hv).2.symm.trans (mem_distanceLayer.mp hi).2)

/-- Distinct layers of one parity have no edges between them. -/
theorem same_parity_layers_anticomplete {V : Type*} [Fintype V]
    {G : SimpleGraph V} {root : V} {i j : ℕ} (hij : i ≠ j) (hparity : i % 2 = j % 2)
    {x y : V} (hx : x ∈ distanceLayer G root i) (hy : y ∈ distanceLayer G root j) :
    ¬ G.Adj x y := by
  intro h
  have hdiff := h.diff_dist_adj (u := root)
  rw [(mem_distanceLayer.mp hx).2, (mem_distanceLayer.mp hy).2] at hdiff
  omega

/-- Neighbours of a vertex in layer `i` belong to one of the first
`i + 2` layers. -/
theorem distanceLayer_neighbor_le {V : Type*} [Fintype V]
    {G : SimpleGraph V} {root x y : V} {i : ℕ}
    (hx : x ∈ distanceLayer G root i) (hxy : G.Adj x y) :
    ∃ j ≤ i + 1, y ∈ distanceLayer G root j := by
  have hx' := mem_distanceLayer.mp hx
  refine ⟨G.dist root y, ?_, mem_distanceLayer.mpr ⟨hx'.1.trans hxy.reachable, rfl⟩⟩
  have hdiff := hxy.diff_dist_adj (u := root)
  rw [hx'.2] at hdiff
  omega

/-- Alternating maximum-independent-set sums are at most the ambient
independence bound. -/
theorem parity_layer_independence_bound {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (hbound : IndependenceBound G k) (root : V) (i : ℕ) :
    ∑ j ∈ (Finset.range (i + 1)).filter (fun j => j % 2 = i % 2),
      (G.induce (distanceLayer G root j : Set V)).indepNum ≤ k := by
  classical
  let F := (Finset.range (i + 1)).filter (fun j => j % 2 = i % 2)
  let I := fun j => independentOn G (distanceLayer G root j)
  have hind : ∀ j ∈ F, G.IsIndepSet (I j : Set V) := fun j _ => independentOn_independent _ _
  have hdis : (F : Set ℕ).PairwiseDisjoint I := by
    intro j _ l _ hjl
    exact (distanceLayers_disjoint G root hjl).mono
      (independentOn_subset _ _) (independentOn_subset _ _)
  have hanti : ∀ j ∈ F, ∀ l ∈ F, j ≠ l → ∀ x ∈ I j, ∀ y ∈ I l, ¬ G.Adj x y := by
    intro j hj l hl hjl x hx y hy
    apply same_parity_layers_anticomplete hjl
      (((Finset.mem_filter.mp hj).2).trans (Finset.mem_filter.mp hl).2.symm)
    · exact independentOn_subset _ _ hx
    · exact independentOn_subset _ _ hy
  have h := independent_packing hbound F I hind hdis hanti
  simpa only [I, independentOn_card] using h

end CycleClique.Construction

end OAI
