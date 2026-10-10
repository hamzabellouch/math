import Mathlib

namespace OAI

noncomputable section

namespace PiExponent.NormalBasisRigidity

open Set Submodule Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

def IsNormalBasis (v : ι → V) (A : Finset ι) : Prop :=
  LinearIndepOn K v (A : Set ι) ∧ span K (v '' (A : Set ι)) = ⊤

lemma exists_normalBasis_subset [Fintype ι] (v : ι → V) (S : Set ι)
    (hS : span K (v '' S) = ⊤) :
    ∃ A : Finset ι, (A : Set ι) ⊆ S ∧ IsNormalBasis (K := K) v A := by
  classical
  let h := linearIndepOn_empty K v
  let A := h.extend (Set.empty_subset S)
  refine ⟨A.toFinset, ?_, ?_, ?_⟩
  · simpa only [Set.coe_toFinset] using h.extend_subset (Set.empty_subset S)
  · simpa only [Set.coe_toFinset] using h.linearIndepOn_extend (Set.empty_subset S)
  · simpa only [Set.coe_toFinset, A] using
      (h.span_image_extend_eq_span_image (Set.empty_subset S)).trans hS

lemma exists_normalBasis_containing [Fintype ι] (v : ι → V)
    (hv : span K (Set.range v) = ⊤) (i : ι) (hi : v i ≠ 0) :
    ∃ A : Finset ι, i ∈ A ∧ IsNormalBasis (K := K) v A := by
  classical
  have h : LinearIndepOn K v ({i} : Set ι) := by
    exact LinearIndepOn.singleton hi
  let A := h.extend (Set.subset_univ _)
  refine ⟨A.toFinset, ?_, ?_, ?_⟩
  · exact Set.mem_toFinset.mpr (h.subset_extend (Set.subset_univ _) (Set.mem_singleton i))
  · simpa only [Set.coe_toFinset] using h.linearIndepOn_extend (Set.subset_univ _)
  · simpa only [Set.coe_toFinset, Set.image_univ, A] using
      (h.span_image_extend_eq_span_image (Set.subset_univ _)).trans (by simpa using hv)

lemma IsNormalBasis.ne_zero [DecidableEq ι] {v : ι → V} {A : Finset ι}
    (hA : IsNormalBasis (K := K) v A) {i : ι} (hi : i ∈ A) : v i ≠ 0 :=
  hA.1.ne_zero hi

lemma exists_normalBasis_omitting [Fintype ι] (v : ι → V) (i : ι)
    (h : span K (v '' {j | j ≠ i}) = ⊤) :
    ∃ A : Finset ι, i ∉ A ∧ IsNormalBasis (K := K) v A := by
  obtain ⟨A, hA, hB⟩ := exists_normalBasis_subset v {j | j ≠ i} h
  exact ⟨A, fun hi => hA hi rfl, hB⟩

lemma mandatory_not_mem_span [Fintype ι] (v : ι → V)
    (hv : span K (Set.range v) = ⊤) (i : ι)
    (hi : ∀ A, IsNormalBasis (K := K) v A → i ∈ A) :
    v i ∉ span K (v '' {j | j ≠ i}) := by
  intro hmem
  have hspan : span K (v '' {j | j ≠ i}) = ⊤ := by
    apply top_unique
    rw [← hv]
    apply span_le.mpr
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = i
    · subst j
      exact hmem
    · exact subset_span ⟨j, hj, rfl⟩
  obtain ⟨A, hAi, hA⟩ := exists_normalBasis_omitting v i hspan
  exact hAi (hi A hA)

lemma IsNormalBasis.card_eq {v : ι → V} {A : Finset ι}
    (hA : IsNormalBasis (K := K) v A) : A.card = Module.finrank K V := by
  classical
  have hli : LinearIndependent K (fun i : A => v i) := hA.1
  let b : Basis A K V := Basis.mk hli (by
    have hr : Set.range (fun i : A => v i) = v '' (A : Set ι) := by
      ext x
      simp
    rw [hr, hA.2])
  exact (Module.finrank_eq_card_finset_basis b).symm

variable {W : Type*} [AddCommGroup W] [Module K W]

lemma mandatory_coordinate_eq_zero [Fintype ι] (b : Basis ι K V) (q : V →ₗ[K] W)
    (hq : span K (Set.range (fun j => q (b j))) = ⊤) (i : ι)
    (hi : ∀ A, IsNormalBasis (K := K) (fun j => q (b j)) A → i ∈ A)
    (t : V) (ht : q t = 0) : b.repr t i = 0 := by
  classical
  by_contra hti
  let S : Submodule K W := span K ((fun j => q (b j)) '' {j | j ≠ i})
  have hsum : (∑ j ∈ Finset.univ.erase i, b.repr t j • q (b j)) ∈ S := by
    apply S.sum_mem
    intro j hj
    exact S.smul_mem _ (subset_span ⟨j, (Finset.mem_erase.mp hj).1, rfl⟩)
  have hall : (∑ j, b.repr t j • q (b j)) = 0 := by
    calc
      _ = q (∑ j, b.repr t j • b j) := by simp only [map_sum, map_smul]
      _ = 0 := by rw [b.sum_repr, ht]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hall
  have hterm : b.repr t i • q (b i) ∈ S := by
    have heq : b.repr t i • q (b i) = -(∑ j ∈ Finset.univ.erase i,
        b.repr t j • q (b j)) := eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hall)
    rw [heq]
    exact S.neg_mem hsum
  exact mandatory_not_mem_span (fun j => q (b j)) hq i hi
    ((S.smul_mem_iff hti).mp hterm)

lemma largest_nontangent_mandatory {m : ℕ}
    (u v : Fin (m + 1) → V) (hu : span K (Set.range u) = ⊤)
    (hvu : ∀ i, i ≠ 0 → v i = u i)
    (hexclude : ∀ A B : Finset (Fin (m + 1)),
      IsNormalBasis (K := K) u A → IsNormalBasis (K := K) v B →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False)
    (i : Fin (m + 1)) (hi0 : i ≠ 0) (hi : u i ≠ 0)
    (hlarge : ∀ j, i < j → u j = 0)
    (B : Finset (Fin (m + 1))) (hB : IsNormalBasis (K := K) v B) : i ∈ B := by
  classical
  obtain ⟨A, hiA, hA⟩ := exists_normalBasis_containing u hu i hi
  by_contra hiB
  apply hexclude A B hA hB i hi0 hiA hiB
  intro j hj
  have hj0 : j ≠ 0 := by
    intro h
    subst j
    exact (not_lt_of_ge (Fin.zero_le _)) hj
  have hjA : j ∉ A := fun h => hA.ne_zero h (hlarge j hj)
  have hjB : j ∉ B := fun h => hB.ne_zero h ((hvu j hj0).trans (hlarge j hj))
  simp only [hjA, hjB]

lemma weighted_normalBasis_exclusion {m : ℕ}
    (u v : Fin (m + 1) → V) (w cost : Fin (m + 1) → ℝ) (C : ℝ)
    (hcomparison : ∀ A B, IsNormalBasis (K := K) u A →
      IsNormalBasis (K := K) v B → (∏ j ∈ A, w j) ≤ C * ∏ j ∈ B, cost j)
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      C * (∏ j ∈ B, cost j) < ∏ j ∈ A, w j)
    (A B : Finset (Fin (m + 1)))
    (hA : IsNormalBasis (K := K) u A) (hB : IsNormalBasis (K := K) v B)
    (i : Fin (m + 1)) (hi0 : i ≠ 0) (hiA : i ∈ A) (hiB : i ∉ B)
    (hlarge : ∀ j, i < j → (j ∈ A ↔ j ∈ B)) : False := by
  exact (not_lt_of_ge (hcomparison A B hA hB))
    (hseparated A B (hA.card_eq.trans hB.card_eq.symm) i hi0 hiA hiB hlarge)

lemma normalBasis_unique_of_discrepancy_excluded [LinearOrder ι]
    (v : ι → V)
    (hexclude : ∀ A B : Finset ι,
      IsNormalBasis (K := K) v A → IsNormalBasis (K := K) v B →
      ∀ i, i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False)
    (A B : Finset ι) (hA : IsNormalBasis (K := K) v A)
    (hB : IsNormalBasis (K := K) v B) : A = B := by
  classical
  by_contra hne
  let S := (A \ B) ∪ (B \ A)
  have hS : S.Nonempty := by
    by_contra he
    have he' : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    apply hne
    apply Finset.ext
    intro i
    constructor
    · intro hi
      by_contra hn
      have : i ∈ S := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hi, hn⟩)
      simp [he'] at this
    · intro hi
      by_contra hn
      have : i ∈ S := Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hi, hn⟩)
      simp [he'] at this
  let i := S.max' hS
  have hiS : i ∈ S := Finset.max'_mem _ _
  have hlarge : ∀ j, i < j → (j ∈ A ↔ j ∈ B) := by
    intro j hj
    have hjS : j ∉ S := fun h => (not_lt_of_ge (Finset.le_max' _ _ h)) hj
    constructor
    · intro hja
      by_contra hjb
      exact hjS (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hja, hjb⟩))
    · intro hjb
      by_contra hja
      exact hjS (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hjb, hja⟩))
  rcases Finset.mem_union.mp hiS with hi | hi
  · exact hexclude A B hA hB i (Finset.mem_sdiff.mp hi).1
      (Finset.mem_sdiff.mp hi).2 hlarge
  · exact hexclude B A hB hA i (Finset.mem_sdiff.mp hi).1
      (Finset.mem_sdiff.mp hi).2 (fun j hj => (hlarge j hj).symm)

end PiExponent.NormalBasisRigidity

end

end OAI
