import OAI.Probability.FreeIsing.Model

namespace OAI

noncomputable section

namespace Problem367

namespace ConnectedHull

def root (d : ℕ) : TreeVertex d := ⟨[], List.IsChain.nil⟩

def takeVertex {d : ℕ} (v : TreeVertex d) (n : ℕ) : TreeVertex d :=
  ⟨v.1.take n, v.2.take n⟩

@[simp] theorem prefix_zero {d : ℕ} (v : TreeVertex d) : takeVertex v 0 = root d := by
  apply Subtype.ext
  simp [takeVertex, root]

@[simp] theorem prefix_length {d : ℕ} (v : TreeVertex d) :
    takeVertex v v.1.length = v := by
  apply Subtype.ext
  simp [takeVertex]

theorem prefix_adj {d : ℕ} (v : TreeVertex d) {n : ℕ} (hn : n < v.1.length) :
    treeAdj (takeVertex v n) (takeVertex v (n + 1)) := by
  left
  exact ⟨v.1[n], List.take_succ_eq_append_getElem hn⟩

def vertices {d : ℕ} (v : TreeVertex d) : Finset (TreeVertex d) := by
  classical
  exact (Finset.range (v.1.length + 1)).image (takeVertex v)

def hull {d : ℕ} (D : Finset (TreeVertex d)) : Finset (TreeVertex d) := by
  classical
  exact insert (root d) (D.biUnion vertices)

theorem prefix_mem_hull {d : ℕ} {D : Finset (TreeVertex d)} {v : TreeVertex d}
    (hv : v ∈ D) {n : ℕ} (hn : n ≤ v.1.length) : takeVertex v n ∈ hull D := by
  classical
  apply Finset.mem_insert_of_mem
  apply Finset.mem_biUnion.mpr
  refine ⟨v, hv, ?_⟩
  exact Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (by omega), rfl⟩

theorem subset_hull {d : ℕ} (D : Finset (TreeVertex d)) : D ⊆ hull D := by
  intro v hv
  simpa using prefix_mem_hull hv (Nat.le_refl v.1.length)

theorem prefix_paths {d : ℕ} (E : Finset (TreeVertex d)) (v : TreeVertex d)
    (hE : ∀ n ≤ v.1.length, takeVertex v n ∈ E) {n : ℕ} (hn : n ≤ v.1.length) :
    Relation.ReflTransGen (fun x y : TreeVertex d => x ∈ E ∧ y ∈ E ∧ treeAdj x y)
      (root d) (takeVertex v n) ∧
    Relation.ReflTransGen (fun x y : TreeVertex d => x ∈ E ∧ y ∈ E ∧ treeAdj x y)
      (takeVertex v n) (root d) := by
  induction n with
  | zero => simp only [prefix_zero]; exact ⟨.refl, .refl⟩
  | succ n ih =>
    have hn' : n ≤ v.1.length := by omega
    have hlt : n < v.1.length := by omega
    have hadj := prefix_adj v hlt
    have hrev : treeAdj (takeVertex v (n + 1)) (takeVertex v n) := by
      rcases hadj with h | h
      · exact Or.inr h
      · exact Or.inl h
    obtain ⟨hforward, hbackward⟩ := ih hn'
    exact ⟨hforward.trans (.single ⟨hE n hn', hE (n + 1) hn, hadj⟩),
      (Relation.ReflTransGen.single ⟨hE (n + 1) hn, hE n hn', hrev⟩).trans hbackward⟩

theorem hull_paths {d : ℕ} (D : Finset (TreeVertex d)) {v : TreeVertex d}
    (hv : v ∈ hull D) :
    Relation.ReflTransGen
      (fun x y : TreeVertex d => x ∈ hull D ∧ y ∈ hull D ∧ treeAdj x y)
      (root d) v ∧
    Relation.ReflTransGen
      (fun x y : TreeVertex d => x ∈ hull D ∧ y ∈ hull D ∧ treeAdj x y)
      v (root d) := by
  classical
  rcases Finset.mem_insert.mp hv with rfl | hv
  · exact ⟨.refl, .refl⟩
  rcases Finset.mem_biUnion.mp hv with ⟨w, hw, hv⟩
  rcases Finset.mem_image.mp hv with ⟨n, hn, rfl⟩
  apply prefix_paths
  · intro k hk
    exact prefix_mem_hull hw hk
  · have := Finset.mem_range.mp hn
    omega

theorem connected_hull {d : ℕ} (D : Finset (TreeVertex d)) :
    ConnectedFinset (hull D) := by
  classical
  refine ⟨⟨root d, Finset.mem_insert_self _ _⟩, ?_⟩
  intro u hu v hv
  exact (hull_paths D hu).2.trans (hull_paths D hv).1

end ConnectedHull

theorem exists_connectedFinset_superset {d : ℕ} (D : Finset (TreeVertex d)) :
    ∃ E : Finset (TreeVertex d), D ⊆ E ∧ ConnectedFinset E :=
  ⟨ConnectedHull.hull D, ConnectedHull.subset_hull D, ConnectedHull.connected_hull D⟩

end Problem367

end

end OAI
