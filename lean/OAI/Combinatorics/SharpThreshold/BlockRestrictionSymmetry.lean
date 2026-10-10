import OAI.Combinatorics.SharpThreshold.Model

namespace OAI

noncomputable section
namespace Problem313

/-- An edge is free in a block restriction when it touches the block. -/
def EdgeTouches {n : ℕ} (B : Finset (Fin n)) (e : GraphEdge n) : Prop :=
  ∃ v, v ∈ e.val ∧ v ∈ B

/-- The vertex permutation is supported on the block. -/
def SupportedOnBlock {n : ℕ} (B : Finset (Fin n))
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ v, v ∉ B → π v = v

lemma supportedOnBlock_mem_iff {n : ℕ} {B : Finset (Fin n)}
    {π : Equiv.Perm (Fin n)} (hπ : SupportedOnBlock B π) (v : Fin n) :
    π v ∈ B ↔ v ∈ B := by
  constructor
  · intro h
    by_contra hn
    exact hn (by simpa [hπ v hn] using h)
  · intro h
    by_contra hn
    have he := hπ (π v) hn
    have he' : π v = v := π.injective he
    exact hn (he'.symm ▸ h)

lemma supportedOnBlock_symm {n : ℕ} {B : Finset (Fin n)}
    {π : Equiv.Perm (Fin n)} (hπ : SupportedOnBlock B π) :
    SupportedOnBlock B π.symm := by
  intro v hv
  apply π.injective
  simpa using (hπ v hv).symm

lemma block_mem_permEdge_iff {n : ℕ} (π : Equiv.Perm (Fin n))
    (e : GraphEdge n) (v : Fin n) :
    v ∈ (permEdge π e).val ↔ π.symm v ∈ e.val := by
  simp [permEdge]

lemma edgeTouches_permEdge_iff {n : ℕ} {B : Finset (Fin n)}
    {π : Equiv.Perm (Fin n)} (hπ : SupportedOnBlock B π) (e : GraphEdge n) :
    EdgeTouches B (permEdge π e) ↔ EdgeTouches B e := by
  constructor
  · rintro ⟨v, hv, hB⟩
    refine ⟨π.symm v, (block_mem_permEdge_iff π e v).mp hv, ?_⟩
    exact (supportedOnBlock_mem_iff (supportedOnBlock_symm hπ) v).mpr hB
  · rintro ⟨v, hv, hB⟩
    refine ⟨π v, ?_, (supportedOnBlock_mem_iff hπ v).mpr hB⟩
    simpa [block_mem_permEdge_iff] using hv

lemma permEdge_eq_self_of_not_touches {n : ℕ} {B : Finset (Fin n)}
    {π : Equiv.Perm (Fin n)} (hπ : SupportedOnBlock B π)
    (e : GraphEdge n) (he : ¬ EdgeTouches B e) : permEdge π e = e := by
  apply Subtype.ext
  ext v
  rw [block_mem_permEdge_iff]
  constructor
  · intro hv
    have hn : π.symm v ∉ B := fun h => he ⟨π.symm v, hv, h⟩
    have hf := hπ (π.symm v) hn
    have hf' : v = π.symm v := by simpa using hf
    exact hf'.symm ▸ hv
  · intro hv
    have hn : v ∉ B := fun h => he ⟨v, hv, h⟩
    have hf := supportedOnBlock_symm hπ v hn
    simpa [hf] using hv

lemma edgeTouches_iff_not_disjoint {n : ℕ} (B : Finset (Fin n))
    (e : GraphEdge n) : EdgeTouches B e ↔ ¬ Disjoint e.val B := by
  classical
  simp [EdgeTouches, Finset.disjoint_left]

lemma supportedOnBlock_one {n : ℕ} (B : Finset (Fin n)) :
    SupportedOnBlock B (1 : Equiv.Perm (Fin n)) := by
  intro v _
  rfl

lemma supportedOnBlock_mul {n : ℕ} {B : Finset (Fin n)}
    {π σ : Equiv.Perm (Fin n)} (hπ : SupportedOnBlock B π)
    (hσ : SupportedOnBlock B σ) : SupportedOnBlock B (π * σ) := by
  intro v hv
  change π (σ v) = v
  rw [hσ v hv, hπ v hv]

/-- The subgroup of permutations supported on a given vertex block. -/
def blockPermutationSubgroup {n : ℕ} (B : Finset (Fin n)) :
    Subgroup (Equiv.Perm (Fin n)) where
  carrier := {π | SupportedOnBlock B π}
  one_mem' := supportedOnBlock_one B
  mul_mem' := supportedOnBlock_mul
  inv_mem' := supportedOnBlock_symm

@[simp] lemma mem_blockPermutationSubgroup {n : ℕ} (B : Finset (Fin n))
    (π : Equiv.Perm (Fin n)) : π ∈ blockPermutationSubgroup B ↔ SupportedOnBlock B π :=
  Iff.rfl

lemma supportedOnBlock_swap {n : ℕ} {B : Finset (Fin n)} {u v : Fin n}
    (hu : u ∈ B) (hv : v ∈ B) : SupportedOnBlock B (Equiv.swap u v) := by
  intro w hw
  have hwu : w ≠ u := fun h => hw (h ▸ hu)
  have hwv : w ≠ v := fun h => hw (h ▸ hv)
  simp [Equiv.swap_apply_def, hwu, hwv]

end Problem313

end

end OAI
