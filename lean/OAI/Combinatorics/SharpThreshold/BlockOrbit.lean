import OAI.Combinatorics.SharpThreshold.Model

namespace OAI

universe u

noncomputable section

namespace Problem313

/-- A permutation of a block, extended by the identity away from the block. -/
def extendBlockPerm {α : Type u} [DecidableEq α] (B : Finset α)
    (σ : Equiv.Perm B) : Equiv.Perm α :=
  σ.extendDomain (Equiv.refl B)

@[simp]
theorem extendBlockPerm_apply_mem {α : Type u} [DecidableEq α]
    (B : Finset α) (σ : Equiv.Perm B) (x : B) :
    extendBlockPerm B σ x = (σ x : α) := by
  exact Equiv.Perm.extendDomain_apply_image σ (Equiv.refl B) x

@[simp]
theorem extendBlockPerm_apply_notMem {α : Type u} [DecidableEq α]
    (B : Finset α) (σ : Equiv.Perm B) (x : α) (hx : x ∉ B) :
    extendBlockPerm B σ x = x := by
  exact Equiv.Perm.extendDomain_apply_not_subtype σ (Equiv.refl B) hx

/-- Equal-sized subsets of a block can be mapped to one another while fixing its complement. -/
theorem exists_blockPerm_map {α : Type u} [DecidableEq α]
    (B s t : Finset α) (hs : s ⊆ B) (ht : t ⊆ B) (hc : s.card = t.card) :
    ∃ σ : Equiv.Perm B, s.map (extendBlockPerm B σ).toEmbedding = t := by
  classical
  have hs' : s.filter (· ∈ B) = s := Finset.filter_true_of_mem (fun _ hx => hs hx)
  have ht' : t.filter (· ∈ B) = t := Finset.filter_true_of_mem (fun _ hx => ht hx)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq
    (s.subtype (· ∈ B)) (t.subtype (· ∈ B)) (by simpa [hs', ht'] using hc)
  refine ⟨σ, ?_⟩
  have hmap := congrArg (fun u : Finset B => u.map (Function.Embedding.subtype _)) hσ
  rw [Finset.subtype_map, ht'] at hmap
  rw [← Finset.subtype_map_of_mem (fun _ hx => hs hx)]
  simp only [Finset.map_map] at *
  convert hmap using 1
  congr 1
  ext x
  simp

/-- A block permutation fixes any finite set disjoint from the block. -/
theorem extendBlockPerm_map_disjoint {α : Type u} [DecidableEq α]
    (B s : Finset α) (σ : Equiv.Perm B) (hs : Disjoint s B) :
    s.map (extendBlockPerm B σ).toEmbedding = s := by
  classical
  have hfix : ∀ x ∈ s, extendBlockPerm B σ x = x := fun x hx =>
    extendBlockPerm_apply_notMem B σ x (Finset.disjoint_left.mp hs hx)
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hx
    change extendBlockPerm B σ y = x at hxy
    rw [hfix y hy] at hxy
    exact hxy ▸ hy
  · intro hx
    exact Finset.mem_map.mpr ⟨x, hx, hfix x hx⟩

/-- Equal-sized finite sets with the same exterior part are in the same block orbit. -/
theorem exists_blockPerm_map_of_sdiff_eq {α : Type u} [DecidableEq α]
    (B s t : Finset α) (hc : s.card = t.card) (hout : s \ B = t \ B) :
    ∃ σ : Equiv.Perm B, s.map (extendBlockPerm B σ).toEmbedding = t := by
  classical
  have hci : (s ∩ B).card = (t ∩ B).card := by
    have hs := Finset.card_sdiff_add_card_inter s B
    have ht := Finset.card_sdiff_add_card_inter t B
    rw [hout, hc] at hs
    omega
  obtain ⟨σ, hσ⟩ := exists_blockPerm_map B (s ∩ B) (t ∩ B)
    Finset.inter_subset_right Finset.inter_subset_right hci
  refine ⟨σ, ?_⟩
  have hs : s = (s ∩ B) ∪ (s \ B) := by ext x; simp; tauto
  calc
    s.map (extendBlockPerm B σ).toEmbedding =
        ((s ∩ B) ∪ (s \ B)).map (extendBlockPerm B σ).toEmbedding := congrArg _ hs
    _ = (t ∩ B) ∪ (t \ B) := by
      rw [Finset.map_union, hσ, extendBlockPerm_map_disjoint B (s \ B) σ
        Finset.sdiff_disjoint, hout]
    _ = t := by ext x; simp; tauto

/-- Edge transport preserving the vertices outside the selected block. -/
theorem exists_blockPerm_permEdge {n : ℕ} (B : Finset (Fin n))
    (e e' : GraphEdge n) (hout : e.1 \ B = e'.1 \ B) :
    ∃ σ : Equiv.Perm B, permEdge (extendBlockPerm B σ) e = e' := by
  obtain ⟨σ, hσ⟩ := exists_blockPerm_map_of_sdiff_eq B e.1 e'.1
    (e.2.trans e'.2.symm) hout
  exact ⟨σ, Subtype.ext hσ⟩

/-- Every edge not touching the block is fixed pointwise by the block action. -/
theorem permEdge_extendBlockPerm_of_disjoint {n : ℕ} (B : Finset (Fin n))
    (σ : Equiv.Perm B) (e : GraphEdge n) (he : Disjoint e.1 B) :
    permEdge (extendBlockPerm B σ) e = e := by
  exact Subtype.ext (extendBlockPerm_map_disjoint B e.1 σ he)

@[simp]
theorem extendBlockPerm_mem_iff {α : Type u} [DecidableEq α]
    (B : Finset α) (σ : Equiv.Perm B) (x : α) :
    extendBlockPerm B σ x ∈ B ↔ x ∈ B := by
  by_cases hx : x ∈ B
  · have h := extendBlockPerm_apply_mem B σ ⟨x, hx⟩
    rw [h]
    exact iff_of_true (σ ⟨x, hx⟩).2 hx
  · simp [extendBlockPerm_apply_notMem B σ x hx, hx]

@[simp]
theorem extendBlockPerm_map_block {α : Type u} [DecidableEq α]
    (B : Finset α) (σ : Equiv.Perm B) :
    B.map (extendBlockPerm B σ).toEmbedding = B := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact (extendBlockPerm_mem_iff B σ y).mpr hy
  · simp

/-- Block-supported permutations leave the exterior part of every finite set unchanged. -/
theorem extendBlockPerm_sdiff {α : Type u} [DecidableEq α]
    (B s : Finset α) (σ : Equiv.Perm B) :
    s.map (extendBlockPerm B σ).toEmbedding \ B = s \ B := by
  calc
    s.map (extendBlockPerm B σ).toEmbedding \ B =
        (s \ B).map (extendBlockPerm B σ).toEmbedding := by
      rw [Finset.map_sdiff, extendBlockPerm_map_block]
    _ = s \ B := extendBlockPerm_map_disjoint B (s \ B) σ Finset.sdiff_disjoint

/-- Two graph edges belong to the same block orbit exactly when their exterior vertices agree. -/
theorem exists_blockPerm_permEdge_iff {n : ℕ} (B : Finset (Fin n))
    (e e' : GraphEdge n) :
    (∃ σ : Equiv.Perm B, permEdge (extendBlockPerm B σ) e = e') ↔
      e.1 \ B = e'.1 \ B := by
  constructor
  · rintro ⟨σ, rfl⟩
    exact (extendBlockPerm_sdiff B e.1 σ).symm
  · exact exists_blockPerm_permEdge B e e'

@[simp]
theorem extendBlockPerm_symm {α : Type u} [DecidableEq α]
    (B : Finset α) (σ : Equiv.Perm B) :
    (extendBlockPerm B σ).symm = extendBlockPerm B σ.symm := by
  exact Equiv.Perm.extendDomain_symm σ (Equiv.refl B)

/-- Relabeling inside the block leaves each exterior configuration coordinate unchanged. -/
theorem permuteConfig_extendBlockPerm_apply_of_disjoint {n : ℕ}
    (B : Finset (Fin n)) (σ : Equiv.Perm B) (x : GraphConfig n)
    (e : GraphEdge n) (he : Disjoint e.1 B) :
    permuteConfig (extendBlockPerm B σ) x e = x e := by
  rw [permuteConfig, extendBlockPerm_symm,
    permEdge_extendBlockPerm_of_disjoint B σ.symm e he]

end Problem313

end

end OAI
