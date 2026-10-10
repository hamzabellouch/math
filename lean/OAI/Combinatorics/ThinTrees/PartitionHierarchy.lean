import OAI.Combinatorics.ThinTrees.ChainEdges

namespace OAI

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset
variable {n m : ℕ} (G : MultiGraph n m)

lemma connectedOn_cut {A S : Finset (Fin n)} {T : Finset (Fin m)}
    (hc : G.ConnectedOn A T) (hS : S.Nonempty) (hSA : S ⊂ A) : (G.cut T S).Nonempty := by
  classical
  by_contra hcut
  have hempty : G.cut T S=∅ := not_nonempty_iff_eq_empty.mp hcut
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑u ∈ S, LinearMap.proj u
  have hker : G.edgeSpan T ≤ LinearMap.ker f := by
    apply (Packing.span_le_iff G.incidence).mpr
    intro e he
    have hiff : G.left e ∈ S ↔ G.right e ∈ S := by
      have hh : ¬((G.left e ∈ S ∧ G.right e ∉ S) ∨ (G.right e ∈ S ∧ G.left e ∉ S)) := by
        intro h
        have hm : e ∈ G.cut T S := mem_filter.mpr ⟨he,h⟩
        simp [hempty] at hm
      tauto
    change f (G.incidence e)=0
    rw [incidence,map_sub]
    change (∑u ∈ S, LinearMap.proj u : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point (G.left e)) -
      (∑u ∈ S, LinearMap.proj u : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point (G.right e))=0
    simp only [sumOn_point,hiff,sub_self]
  obtain ⟨u,hu⟩ := hS
  have hv : (A \ S).Nonempty := sdiff_nonempty.mpr (not_subset.mpr (by
    by_contra h
    push Not at h
    exact (not_ssubset_of_subset h) hSA))
  obtain ⟨v,hv⟩ := hv
  obtain ⟨hvA,hvS⟩ := mem_sdiff.mp hv
  have hz := hker (hc u (hSA.subset hu) v hvA)
  change f (point u-point v)=0 at hz
  rw [map_sub] at hz
  change (∑w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point u) -
    (∑w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point v)=0 at hz
  simp [sumOn_point,hu,hvS] at hz

lemma packableOn_edgeConnectedReal {F : Finset (Fin m)} {q : ℕ} {A : Finset (Fin n)}
    (hp : G.PackableOn F q A) : G.EdgeConnectedReal A q := by
  classical
  obtain ⟨T,hT,hd⟩ := hp
  intro S hS hSA
  have hne (i : Fin q) := G.connectedOn_cut (hT i).2 hS hSA
  have hdis : (↑(univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint (fun i => G.cut (T i) S) := by
    intro i _ j _ hij
    exact disjoint_of_subset_left (filter_subset _ _) (disjoint_of_subset_right (filter_subset _ _) (hd hij))
  have hsub : univ.biUnion (fun i : Fin q => G.cut (T i) S) ⊆ G.cut (G.inducedEdges A) S := by
    apply biUnion_subset.mpr
    intro i _ e he
    obtain ⟨het,hes⟩ := mem_filter.mp he
    have hh := (mem_filter.mp ((hT i).1 het)).2
    exact mem_filter.mpr ⟨(G.mem_inducedEdges A e).mpr hh,hes⟩
  have hh := card_le_card hsub
  rw [card_biUnion hdis] at hh
  have hl : q ≤ ∑i : Fin q, (G.cut (T i) S).card := by
    simpa using sum_le_sum (s := (univ : Finset (Fin q))) (f := fun _ => 1)
      (g := fun i => (G.cut (T i) S).card) (fun i _ => card_pos.mpr (hne i))
  exact_mod_cast hl.trans hh

lemma packingParts_vertexPartition (F : Finset (Fin m)) (q : ℕ) :
    VertexPartition univ (G.packingParts F q) := by
  obtain ⟨hn,hd,hc⟩ := G.packingParts_partition F q
  exact ⟨fun A hA => ⟨(hn A hA).1,subset_univ _⟩,hd,hc⟩

lemma packingParts_local (F : Finset (Fin m)) (q : ℕ) :
    ∀A ∈ G.packingParts F q, G.EdgeConnectedReal A q := by
  intro A hA
  exact G.packableOn_edgeConnectedReal ((G.packingParts_partition F q).1 A hA).2

lemma packingParts_eq_root {F : Finset (Fin m)} {q : ℕ} (hn : 0 < n)
    (hp : G.TreePackable F q) : G.packingParts F q={univ} := by
  classical
  have hu : (univ : Finset (Fin n)).Nonempty := ⟨⟨0,hn⟩,mem_univ _⟩
  have hmax : G.MaxPackable F q univ := ⟨hu,(G.packableOn_univ F q).mpr hp,
    fun B hB _ => (Subset.antisymm (subset_univ _) hB)⟩
  have hr : univ ∈ G.packingParts F q := mem_filter.mpr ⟨mem_univ _,hmax⟩
  apply Subset.antisymm
  · intro A hA
    apply mem_singleton.mpr
    rcases G.maxPackable_disjoint (mem_filter.mp hA).2 hmax with h | h
    · exact h
    · obtain ⟨v,hv⟩ := ((G.packingParts_partition F q).1 A hA).1
      exact False.elim (disjoint_left.mp h hv (mem_univ _))
  · exact singleton_subset_iff.mpr hr

end
end StrongThinTree.MultiGraph

end

end OAI
