import Mathlib.Combinatorics.Matroid.Closure

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set

variable {α : Type*} {M : Matroid α} {I J : Set α} {e : α}

def support (M : Matroid α) (I : Set α) (e : α) : Set α :=
  ⋂₀ {J | J ⊆ I ∧ e ∈ M.closure J}

lemma support_subset (he : e ∈ M.closure I) : support M I e ⊆ I :=
  Set.sInter_subset_of_mem ⟨Subset.rfl, he⟩

lemma support_subset_of_mem_closure (hJI : J ⊆ I) (he : e ∈ M.closure J) :
    support M I e ⊆ J :=
  Set.sInter_subset_of_mem ⟨hJI, he⟩

lemma mem_closure_support (hI : M.Indep I) (he : e ∈ M.closure I) :
    e ∈ M.closure (support M I e) := by
  rw [support, hI.closure_sInter_eq_biInter_closure_of_forall_subset
    (Js := {J | J ⊆ I ∧ e ∈ M.closure J})
    ⟨I, Subset.rfl, he⟩ (fun _ hJ => hJ.1)]
  exact Set.mem_iInter₂.mpr (fun _ hJ => hJ.2)

lemma mem_closure_iff_support_subset (hI : M.Indep I)
    (he : e ∈ M.closure I) (hJI : J ⊆ I) :
    e ∈ M.closure J ↔ support M I e ⊆ J := by
  constructor
  · exact support_subset_of_mem_closure hJI
  · intro h
    exact M.closure_subset_closure h (mem_closure_support hI he)

lemma support_nonempty (hI : M.Indep I) (he : e ∈ M.closure I)
    (hne : e ∉ M.closure ∅) : (support M I e).Nonempty := by
  by_contra h
  have hem := mem_closure_support hI he
  rw [Set.not_nonempty_iff_eq_empty.mp h] at hem
  exact hne hem

lemma support_unique (hI : M.Indep I) (he : e ∈ M.closure I)
    (hJI : J ⊆ I) (hJe : e ∈ M.closure J)
    (hmin : ∀ K ⊆ I, e ∈ M.closure K → J ⊆ K) : J = support M I e := by
  exact Set.Subset.antisymm
    (hmin _ (support_subset he) (mem_closure_support hI he))
    (support_subset_of_mem_closure hJI hJe)

lemma old_redundant_after_insertions (he : e ∈ M.closure I) (A : Set α) :
    M.closure (insert e (I ∪ A)) = M.closure (I ∪ A) := by
  exact M.closure_insert_eq_of_mem_closure
    (M.closure_subset_closure Set.subset_union_left he)

lemma mem_closure_prefix_iff (hI : M.Indep I) (he : e ∈ M.closure I)
    (time : α → ℕ) (k : ℕ) :
    e ∈ M.closure {x | x ∈ I ∧ time x ≤ k} ↔
      ∀ x ∈ support M I e, time x ≤ k := by
  rw [mem_closure_iff_support_subset hI he (fun _ hx => hx.1)]
  constructor
  · intro h x hx
    exact (h hx).2
  · intro h x hx
    exact ⟨support_subset he hx, h x hx⟩

end Pivots
end MatroidProphet

end OAI
