import Mathlib

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction

abbrev Labels := Fin 10
abbrev Family := Finset Labels → Prop

attribute [local instance] Classical.propDecidable

structure TenSystem (T Q : Family) : Prop where
  tetra_card : ∀ S, Q S → S.card = 4
  down : ∀ S U, Q S → U ⊆ S → U.card = 3 → T U
  pure : ∀ U, T U → ∃ S, Q S ∧ U ⊆ S
  no_boundary : ∀ S U, Q S → U ⊆ S → U.card = 3 →
    ∃ S', Q S' ∧ U ⊆ S' ∧ S' ≠ S
  complementary : ∀ S U, Q S → U ⊆ Sᶜ → U.card = 3 →
    (T U ↔ ¬ T (Sᶜ \ U))
  pair_count : ∀ S P, Q S → P ⊆ Sᶜ → P.card = 2 →
    ((Sᶜ \ P).filter (fun w => T (insert w P))).card = 2

variable {T Q : Family}

lemma filter_card_eq_two_three_pos {s r : Finset Labels} {p : Labels → Prop}
    [DecidablePred p] (hs : s.card = 4) (hr : r.card = 3) (hrs : r ⊆ s)
    (hp : (s.filter p).card = 2) : ∃ x ∈ r, p x := by
  by_contra hn
  have hsub : s.filter p ⊆ s \ r := by
    intro x hx
    obtain ⟨hxs, hpx⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_sdiff.mpr ⟨hxs, ?_⟩
    intro hxr
    exact hn ⟨x, hxr, hpx⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset hrs, hs, hr, hp] at hc
  norm_num at hc

lemma filter_card_eq_two_three_neg {s r : Finset Labels} {p : Labels → Prop}
    [DecidablePred p] (hr : r.card = 3) (hrs : r ⊆ s)
    (hp : (s.filter p).card = 2) : ∃ x ∈ r, ¬ p x := by
  by_contra hn
  have hsub : r ⊆ s.filter p := by
    intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨hrs hx, ?_⟩
    by_contra hnp
    exact hn ⟨x, hx, hnp⟩
  have hc := Finset.card_le_card hsub
  rw [hr, hp] at hc
  norm_num at hc

lemma three_pos (h : TenSystem T Q) (S P R : Finset Labels)
    (hS : Q S) (hP : P ⊆ Sᶜ) (hcP : P.card = 2)
    (hR : R ⊆ Sᶜ \ P) (hcR : R.card = 3) :
    ∃ w ∈ R, T (insert w P) := by
  classical
  apply filter_card_eq_two_three_pos (s := Sᶜ \ P) (r := R) ?_ hcR hR
    (h.pair_count S P hS hP hcP)
  rw [Finset.card_sdiff_of_subset hP, Finset.card_compl, h.tetra_card S hS, hcP]
  decide

lemma three_neg (h : TenSystem T Q) (S P R : Finset Labels)
    (hS : Q S) (hP : P ⊆ Sᶜ) (hcP : P.card = 2)
    (hR : R ⊆ Sᶜ \ P) (hcR : R.card = 3) :
    ∃ w ∈ R, ¬ T (insert w P) := by
  classical
  exact filter_card_eq_two_three_neg hcR hR (h.pair_count S P hS hP hcP)

lemma tetra_extension {S U : Finset Labels} (hU : U ⊆ S)
    (hcS : S.card = 4) (hcU : U.card = 3) :
    ∃ v, v ∉ U ∧ S = insert v U := by
  have hcard : (S \ U).card = 1 := by
    rw [Finset.card_sdiff_of_subset hU, hcS, hcU]
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
  have hm : v ∈ S \ U := by rw [hv]; simp
  refine ⟨v, (Finset.mem_sdiff.mp hm).2, ?_⟩
  have he := Finset.sdiff_union_of_subset hU
  rw [hv] at he
  simpa using he.symm

@[simp] lemma map_compl (e : Equiv.Perm Labels) (S : Finset Labels) :
    Sᶜ.map e.toEmbedding = (S.map e.toEmbedding)ᶜ := by
  ext x
  simp

@[simp] lemma map_symm_map (e : Equiv.Perm Labels) (S : Finset Labels) :
    (S.map e.symm.toEmbedding).map e.toEmbedding = S := by
  ext x
  simp

@[simp] lemma symm_map_map (e : Equiv.Perm Labels) (S : Finset Labels) :
    (S.map e.toEmbedding).map e.symm.toEmbedding = S := by
  ext x
  simp

lemma TenSystem.relabel (h : TenSystem T Q) (e : Equiv.Perm Labels) :
    TenSystem (fun U => T (U.map e.toEmbedding))
      (fun S => Q (S.map e.toEmbedding)) := by
  constructor
  · intro S hS
    simpa using h.tetra_card _ hS
  · intro S U hS hUS hcU
    exact h.down _ _ hS (Finset.map_subset_map.mpr hUS) (by simpa using hcU)
  · intro U hU
    obtain ⟨S, hS, hUS⟩ := h.pure _ hU
    refine ⟨S.map e.symm.toEmbedding, ?_, ?_⟩
    · simpa using hS
    · have hh := (Finset.map_subset_map (f := e.symm.toEmbedding)).mpr hUS
      simpa using hh
  · intro S U hS hUS hcU
    obtain ⟨S', hS', hUS', hne⟩ := h.no_boundary _ _ hS
      (Finset.map_subset_map.mpr hUS) (by simpa using hcU)
    refine ⟨S'.map e.symm.toEmbedding, ?_, ?_, ?_⟩
    · simpa using hS'
    · have hh := (Finset.map_subset_map (f := e.symm.toEmbedding)).mpr hUS'
      simpa using hh
    · intro he
      have hh := congrArg (Finset.map e.toEmbedding) he
      exact hne (by simpa using hh)
  · intro S U hS hUS hcU
    have hh := h.complementary _ _ hS
      (show U.map e.toEmbedding ⊆ (S.map e.toEmbedding)ᶜ by
        rw [← map_compl]
        exact Finset.map_subset_map.mpr hUS)
      (by simpa using hcU)
    simpa [Finset.map_sdiff] using hh
  · intro S P hS hPS hcP
    have hh := h.pair_count _ _ hS
      (show P.map e.toEmbedding ⊆ (S.map e.toEmbedding)ᶜ by
        rw [← map_compl]
        exact Finset.map_subset_map.mpr hPS)
      (by simpa using hcP)
    rw [← map_compl, ← Finset.map_sdiff, Finset.filter_map, Finset.card_map] at hh
    simpa only [Function.comp_apply, Finset.map_insert] using hh

end BorsukNine.FiniteObstruction

end OAI
