import OAI.Probability.SignedSweeps.Irreducibility

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
variable {A : Type*} [Fintype A] [DecidableEq A]
attribute [local instance] Classical.propDecidable

def edgeEnds (e : A × A) : Finset A := {e.1, e.2}

def matchingVertices (M : Finset (A × A)) : Finset A := M.biUnion edgeEnds

def DisjointEdgeMatching (G : SimpleGraph A) (S : Finset A) (M : Finset (A × A)) : Prop :=
  (∀ e ∈ M, G.Adj e.1 e.2 ∧ e.1 ∈ S ∧ e.2 ∈ S) ∧
    (M : Set (A × A)).PairwiseDisjoint edgeEnds

def neighborUnion (G : SimpleGraph A) (S : Finset A) : Finset A :=
  Finset.univ.filter (fun y => ∃ x ∈ S, G.Adj x y)

omit [Fintype A] [DecidableEq A] in
lemma mem_neighborUnion [Fintype A] [DecidableEq A]
    {G : SimpleGraph A} {S : Finset A} {y : A} :
    y ∈ neighborUnion G S ↔ ∃ x ∈ S, G.Adj x y := by simp [neighborUnion]

omit [Fintype A] [DecidableEq A] in
lemma matching_vertices_sub [Fintype A] [DecidableEq A]
    {G : SimpleGraph A} {S : Finset A} {M : Finset (A × A)}
    (hM : DisjointEdgeMatching G S M) : matchingVertices M ⊆ S := by
  intro x hx
  obtain ⟨e, he, hx⟩ := Finset.mem_biUnion.mp hx
  rcases Finset.mem_insert.mp hx with hx | hx
  · exact hx ▸ (hM.1 e he).2.1
  · exact (Finset.mem_singleton.mp hx) ▸ (hM.1 e he).2.2

omit [Fintype A] [DecidableEq A] in
lemma matching_augment [Fintype A] [DecidableEq A]
    {G : SimpleGraph A} {S : Finset A} {M : Finset (A × A)}
    (hM : DisjointEdgeMatching G S M) {u v : A} (hu : u ∈ S) (hv : v ∈ S)
    (huM : u ∉ matchingVertices M) (hvM : v ∉ matchingVertices M) (huv : G.Adj u v) :
    DisjointEdgeMatching G S (insert (u,v) M) := by
  have hd : Disjoint (edgeEnds (u,v)) (matchingVertices M) := by
    apply Finset.disjoint_left.mpr
    intro x hx hxM
    rcases (show x = u ∨ x = v by simpa [edgeEnds] using hx) with rfl | rfl
    · exact huM hxM
    · exact hvM hxM
  refine ⟨?_, ?_⟩
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact ⟨huv, hu, hv⟩
    · exact hM.1 e he
  · intro e he f hf hef
    rcases Finset.mem_insert.mp he with rfl | he
    · have hf : f ∈ M := (Finset.mem_insert.mp hf).resolve_left (Ne.symm hef)
      exact (Finset.disjoint_biUnion_right _ _ _).mp hd f hf
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · exact ((Finset.disjoint_biUnion_right _ _ _).mp hd e he).symm
      · exact hM.2 he hf hef

lemma exists_dominating_matching (G : SimpleGraph A) (S : Finset A)
    (hS : ∀ x ∈ S, ∃ y ∈ S, G.Adj x y) :
    ∃ M : Finset (A × A), DisjointEdgeMatching G S M ∧
      S \ matchingVertices M ⊆ neighborUnion G (matchingVertices M) := by
  let F : Finset (Finset (A × A)) := Finset.univ.filter (DisjointEdgeMatching G S)
  have hne : F.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨by simp, by simp [Set.PairwiseDisjoint]⟩
  obtain ⟨M, hMF, hmax⟩ := F.exists_max_image Finset.card hne
  have hM : DisjointEdgeMatching G S M := (Finset.mem_filter.mp hMF).2
  refine ⟨M, hM, ?_⟩
  intro x hx
  obtain ⟨hxS, hxM⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨y, hyS, hxy⟩ := hS x hxS
  have hyM : y ∈ matchingVertices M := by
    by_contra hyM
    have hnew := matching_augment hM hxS hyS hxM hyM hxy
    have hneM : (x,y) ∉ M := by
      intro hxyM
      exact hxM (Finset.mem_biUnion.mpr ⟨(x,y), hxyM, by simp [edgeEnds]⟩)
    have h := hmax (insert (x,y) M) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnew⟩)
    rw [Finset.card_insert_of_notMem hneM] at h
    omega
  exact mem_neighborUnion.mpr ⟨y, hyM, hxy.symm⟩

omit [Fintype A] [DecidableEq A] in
lemma matching_weight_factorization [Fintype A] [DecidableEq A]
    {G : SimpleGraph A} {S : Finset A} {M : Finset (A × A)}
    (hM : DisjointEdgeMatching G S M) (w : A → ℝ) :
    (∏ x ∈ matchingVertices M, w x) = ∏ e ∈ M, (w e.1 * w e.2) := by
  rw [matchingVertices, Finset.prod_biUnion hM.2]
  apply Finset.prod_congr rfl
  intro e he
  have hne : e.1 ≠ e.2 := (hM.1 e he).1.ne
  simp [edgeEnds, hne]

omit [Fintype A] [DecidableEq A] in
lemma matching_vertices_card [Fintype A] [DecidableEq A]
    {G : SimpleGraph A} {S : Finset A} {M : Finset (A × A)}
    (hM : DisjointEdgeMatching G S M) : (matchingVertices M).card = 2 * M.card := by
  rw [matchingVertices, Finset.card_biUnion hM.2]
  simp only [edgeEnds]
  have hc (e : A × A) (he : e ∈ M) : ({e.1, e.2} : Finset A).card = 2 := by
    have hne : e.1 ≠ e.2 := (hM.1 e he).1.ne
    simp [hne]
  rw [Finset.sum_congr rfl hc]
  simp [mul_comm]

lemma neighborUnion_weight_bound (G : SimpleGraph A) (S : Finset A) (w : A → ℝ)
    (hw : ∀ x, 0 ≤ w x) {Δ : ℝ}
    (hdeg : ∀ x, (∑ y ∈ Finset.univ.filter (G.Adj x), w y) ≤ Δ) :
    (∑ y ∈ neighborUnion G S, w y) ≤ (S.card : ℝ) * Δ := by
  calc
    _ ≤ ∑ y ∈ neighborUnion G S, ∑ x ∈ S, if G.Adj x y then w y else 0 := by
      apply Finset.sum_le_sum
      intro y hy
      obtain ⟨x, hx, hxy⟩ := mem_neighborUnion.mp hy
      exact (Finset.single_le_sum (fun z _ => by split_ifs; exact hw _; exact le_refl 0) hx).trans'
        (by simp only [ite_eq_left hxy]; exact le_refl _)
    _ = ∑ x ∈ S, ∑ y ∈ neighborUnion G S, if G.Adj x y then w y else 0 := Finset.sum_comm
    _ ≤ ∑ x ∈ S, ∑ y, if G.Adj x y then w y else 0 := by
      apply Finset.sum_le_sum
      intro x _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
        intros; split_ifs; exact hw _; exact le_refl 0)
    _ ≤ ∑ x ∈ S, Δ := by
      apply Finset.sum_le_sum
      intro x _
      simpa only [Finset.sum_filter] using hdeg x
    _ = _ := by simp

end SignedSweeps
end

end OAI
