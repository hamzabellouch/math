import OAI.Combinatorics.GraphThreshold.GraphSupport
import OAI.Combinatorics.GraphThreshold.GraphProbability
import OAI.Combinatorics.GraphThreshold.CopyOrbits
import OAI.Combinatorics.GraphThreshold.GraphExpectedCopies

namespace OAI

noncomputable section

open scoped Pointwise

namespace LeanBlast.SecondKahnKalai

variable {n : ℕ}

theorem mem_copyOrbit_iff_edgeSupportGraph_iso {S T : Finset (Edge n)} :
    T ∈ copyOrbit (Equiv.Perm (Fin n)) S ↔
      Nonempty (edgeSupportGraph S ≃g edgeSupportGraph T) := by
  rw [mem_copyOrbit_iff]
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨edgeSupportGraph_smulIso σ S⟩
  · rintro ⟨e⟩
    exact exists_smul_eq_of_edgeSupportGraph_iso e

/-- Distinct edge orbits correspond bijectively to actual unlabelled subgraphs.
The target has no isolated vertices, so its image subgraph is uniquely determined
by its edges. This also covers the empty graph, with its empty vertex set. -/
def orbitSubgraphEquiv (S : Finset (Edge n)) :
    OrbitCopy (Equiv.Perm (Fin n)) S ≃
      {K : (⊤ : SimpleGraph (Fin n)).Subgraph //
        Nonempty (edgeSupportGraph S ≃g K.coe)} where
  toFun T := ⟨edgeSubgraph T.val, mem_copyOrbit_iff_edgeSupportGraph_iso.mp T.property⟩
  invFun K := ⟨graphEdges K.val.spanningCoe, by
    apply mem_copyOrbit_iff_edgeSupportGraph_iso.mpr
    obtain ⟨e⟩ := K.property
    have hK := subgraph_eq_edgeSubgraph_of_iso K.val e
    change Nonempty (edgeSupportGraph S ≃g (edgeSubgraph _).coe)
    rw [← hK]
    exact ⟨e⟩⟩
  left_inv T := by
    apply Subtype.ext
    exact graphEdges_graphOfEdges T.val
  right_inv K := by
    apply Subtype.ext
    exact (subgraph_eq_edgeSubgraph_of_iso K.val K.property.some).symm

theorem orbitCount_eq_copyCount (S : Finset (Edge n)) :
    orbitCount (Equiv.Perm (Fin n)) S =
      (⊤ : SimpleGraph (Fin n)).copyCount (edgeSupportGraph S) := by
  classical
  calc
    orbitCount (Equiv.Perm (Fin n)) S =
        Fintype.card (OrbitCopy (Equiv.Perm (Fin n)) S) := (card_OrbitCopy _ _).symm
    _ = Fintype.card {K : (⊤ : SimpleGraph (Fin n)).Subgraph //
        Nonempty (edgeSupportGraph S ≃g K.coe)} := Fintype.card_congr (orbitSubgraphEquiv S)
    _ = _ := by
      rw [SimpleGraph.copyCount, Fintype.card_subtype]
      apply congrArg Finset.card
      ext K
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem expectedCopies_edgeSupportGraph (p : ℝ) (S : Finset (Edge n)) :
    expectedCopies n p (edgeSupportGraph S) =
      (orbitCount (Equiv.Perm (Fin n)) S : ℝ) * p ^ S.card := by
  rw [expectedCopies_formula, edgeCount_edgeSupportGraph, orbitCount_eq_copyCount]

/-- The internal orbit constraint follows from an actual subgraph constraint
of the public expectation threshold, with no multiplicity factor. -/
theorem orbit_expectation_constraint {V : Type*} (f : V ↪ Fin n)
    (H : SimpleGraph V) (q : ℝ)
    (hq : ∀ F : H.Subgraph, (1 / 2 : ℝ) ≤ expectedCopies n q F.coe)
    (S : Finset (Edge n)) (hS : S ⊆ graphEdges (H.map f)) :
    (1 / 2 : ℝ) ≤ (orbitCount (Equiv.Perm (Fin n)) S : ℝ) * q ^ S.card := by
  obtain ⟨F, ⟨e⟩⟩ := exists_subgraph_iso_edgeSupportGraph f H S hS
  rw [← expectedCopies_edgeSupportGraph, expectedCopies_iso n q e]
  exact hq F

theorem copyCount_pos_iff_orbit_subset {V : Type*} (f : V ↪ Fin n)
    (H : SimpleGraph V) (W : Finset (Edge n)) :
    0 < (graphOfEdges W).copyCount H ↔
      ∃ E ∈ copyOrbit (Equiv.Perm (Fin n)) (graphEdges (H.map f)), E ⊆ W := by
  rw [copyCount_pos_iff_exists_smul_subset f H W]
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨_, (mem_copyOrbit_iff _).mpr ⟨σ, rfl⟩, hσ⟩
  · rintro ⟨E, hE, hEW⟩
    obtain ⟨σ, rfl⟩ := (mem_copyOrbit_iff _).mp hE
    exact ⟨σ, hEW⟩

theorem exists_graphRepresentationWithConstraints {V : Type*} [Fintype V]
    (n : ℕ) (H : SimpleGraph V) (hcard : Fintype.card V ≤ n) (q : ℝ)
    (hq : ∀ F : H.Subgraph, (1 / 2 : ℝ) ≤ expectedCopies n q F.coe) :
    ∃ E : Finset (Edge n), E.card = edgeCount H ∧
      (∀ W : Finset (Edge n),
        (0 < (graphOfEdges W).copyCount H ↔
          ∃ T ∈ copyOrbit (Equiv.Perm (Fin n)) E, T ⊆ W)) ∧
      (∀ S : Finset (Edge n), S ⊆ E →
        (1 / 2 : ℝ) ≤ (orbitCount (Equiv.Perm (Fin n)) S : ℝ) * q ^ S.card) := by
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card V ≤ Fintype.card (Fin n) by simpa using hcard)
  exact ⟨graphEdges (H.map f), card_mappedGraphEdges f H,
    copyCount_pos_iff_orbit_subset f H, orbit_expectation_constraint f H q hq⟩

end LeanBlast.SecondKahnKalai

end

end OAI
