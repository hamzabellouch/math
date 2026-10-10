import OAI.Probability.SignedSweeps.HilbertBlocks

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

abbrev EvenAllocation (u p : ℕ) := {S : Finset (Fin p) // S.card = u}

lemma allocation_complement_card {u v p : ℕ} (h : u + v = p) (S : EvenAllocation u p) :
    Fintype.card {i : Fin p // i ∉ S.1} = v := by
  have ht := Fintype.card_subtype_compl (fun i : Fin p => i ∈ S.1)
  have he : Fintype.card {i : Fin p // i ∈ S.1} = u := by simpa using S.2
  rw [he, Fintype.card_fin] at ht
  omega

def allocationEquiv {u v p : ℕ} (h : u + v = p) (S : EvenAllocation u p) :
    (Fin u ⊕ Fin v) ≃ Fin p :=
  (Equiv.sumCongr (Finset.equivFinOfCardEq S.2).symm
    (Fintype.equivFinOfCardEq (allocation_complement_card h S)).symm).trans
      (Equiv.sumCompl (fun i : Fin p => i ∈ S.1))

lemma allocationEquiv_left_mem {u v p : ℕ} (h : u + v = p) (S : EvenAllocation u p) (i : Fin u) :
    allocationEquiv h S (Sum.inl i) ∈ S.1 :=
  ((Finset.equivFinOfCardEq S.2).symm i).2

lemma allocationEquiv_right_not_mem {u v p : ℕ} (h : u + v = p)
    (S : EvenAllocation u p) (i : Fin v) : allocationEquiv h S (Sum.inr i) ∉ S.1 :=
  ((Fintype.equivFinOfCardEq (allocation_complement_card h S)).symm i).2

def wordEvenSites {p : ℕ} {C : Type*} (w : Fin p → C ⊕ C) : Finset (Fin p) :=
  Finset.univ.filter (fun i => ∃ c, w i = Sum.inl c)

@[simp] lemma mem_wordEvenSites {p : ℕ} {C : Type*} (w : Fin p → C ⊕ C) (i : Fin p) :
    i ∈ wordEvenSites w ↔ ∃ c, w i = Sum.inl c := by simp [wordEvenSites]

lemma pairColorWord_evenSites {u v p : ℕ} {C : Type*} (h : u + v = p)
    (S : EvenAllocation u p) (w : (Fin u → C) × (Fin v → C)) :
    wordEvenSites (pairColorWord (allocationEquiv h S) w) = S.1 := by
  ext i
  obtain ⟨i, rfl⟩ := (allocationEquiv h S).surjective i
  cases i with
  | inl i =>
    simp only [mem_wordEvenSites, pairColorWord, Function.comp_apply,
      Equiv.symm_apply_apply, Sum.elim_inl, Sum.inl.injEq, exists_eq',
      allocationEquiv_left_mem, iff_self]
  | inr i =>
    simp only [mem_wordEvenSites, pairColorWord, Function.comp_apply,
      Equiv.symm_apply_apply, Sum.elim_inr, Sum.inr_ne_inl, exists_false,
      allocationEquiv_right_not_mem, iff_self]

lemma pairColorEmbedding_disjoint {u v p : ℕ} {C : Type*} (h : u + v = p)
    {S T : EvenAllocation u p} (hST : S ≠ T) :
    Disjoint (Set.range (pairColorEmbedding (C := C) (allocationEquiv h S)))
      (Set.range (pairColorEmbedding (C := C) (allocationEquiv h T))) := by
  rw [Set.disjoint_left]
  rintro _ ⟨w, rfl⟩ ⟨z, he⟩
  have hs := congrArg wordEvenSites he
  change wordEvenSites (pairColorWord (allocationEquiv h T) z) =
    wordEvenSites (pairColorWord (allocationEquiv h S) w) at hs
  rw [pairColorWord_evenSites, pairColorWord_evenSites] at hs
  exact hST (Subtype.ext hs.symm)

lemma pairWordEmbedding_orthogonal {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u + v = p) {S T : EvenAllocation u p} (hST : S ≠ T)
    (x y : WordSpace u C ⊗[ℂ] WordSpace v C) :
    inner ℂ (pairWordEmbedding (allocationEquiv h S) x)
      (pairWordEmbedding (allocationEquiv h T) y) = 0 :=
  euclideanEmbedding_orthogonal _ _ (pairColorEmbedding_disjoint h hST) _ _

lemma pairColorEmbedding_range {u v p : ℕ} {C : Type*} (h : u + v = p)
    (S : EvenAllocation u p) (w : Fin p → C ⊕ C) :
    w ∈ Set.range (pairColorEmbedding (C := C) (allocationEquiv h S)) ↔ wordEvenSites w = S.1 := by
  constructor
  · rintro ⟨z,rfl⟩
    exact pairColorWord_evenSites h S z
  · intro hw
    have he (i : Fin u) : ∃ c, w (allocationEquiv h S (Sum.inl i)) = Sum.inl c := by
      rw [← mem_wordEvenSites, hw]
      exact allocationEquiv_left_mem h S i
    have ho (j : Fin v) : ∃ c, w (allocationEquiv h S (Sum.inr j)) = Sum.inr c := by
      have hnot : allocationEquiv h S (Sum.inr j) ∉ wordEvenSites w := by
        rw [hw]; exact allocationEquiv_right_not_mem h S j
      cases hc : w (allocationEquiv h S (Sum.inr j)) with
      | inl c => exact False.elim (hnot ((mem_wordEvenSites _ _).mpr ⟨c,hc⟩))
      | inr c => exact ⟨c,rfl⟩
    choose z hz using he
    choose t ht using ho
    refine ⟨(z,t), ?_⟩
    funext i
    obtain ⟨i,rfl⟩ := (allocationEquiv h S).surjective i
    cases i with
    | inl i =>
      change Sum.elim (fun i => Sum.inl (z i)) (fun j => Sum.inr (t j))
        ((allocationEquiv h S).symm (allocationEquiv h S (Sum.inl i))) = _
      rw [Equiv.symm_apply_apply]
      exact (hz i).symm
    | inr j =>
      change Sum.elim (fun i => Sum.inl (z i)) (fun j => Sum.inr (t j))
        ((allocationEquiv h S).symm (allocationEquiv h S (Sum.inr j))) = _
      rw [Equiv.symm_apply_apply]
      exact (ht j).symm

end SignedSweeps
end

end OAI
