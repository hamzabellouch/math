import Mathlib

namespace OAI

open scoped BigOperators

namespace Balanced.ReusePatternCounting

noncomputable section
open scoped Classical

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

def changedSet (base f : α → β) : Finset α :=
  Finset.univ.filter (fun i => f i ≠ base i)

def fillOn (base : α → β) (s : Finset α) (v : s → β) (i : α) : β :=
  if hi : i ∈ s then v ⟨i, hi⟩ else base i

omit [Fintype β] in
theorem changedSet_fillOn_subset (base : α → β) (s : Finset α) (v : s → β) :
    changedSet base (fillOn base s v) ⊆ s := by
  intro i hi
  by_contra his
  exact (Finset.mem_filter.mp hi).2 (by simp [fillOn, his])

theorem card_sparse_maps_le (base : α → β) (k : ℕ) (hk : k ≤ Fintype.card α) :
    Fintype.card {f : α → β // (changedSet base f).card ≤ k} ≤
      (Fintype.card α).choose k * Fintype.card β ^ k := by
  let fill : (Σ s : {s : Finset α // s.card = k}, (s.1 → β)) →
      {f : α → β // (changedSet base f).card ≤ k} := fun sv =>
    ⟨fillOn base sv.1.1 sv.2,
      (Finset.card_le_card (changedSet_fillOn_subset base sv.1.1 sv.2)).trans_eq sv.1.2⟩
  have hsurj : Function.Surjective fill := by
    intro f
    obtain ⟨s, hsub, hcard⟩ := Finset.exists_superset_card_eq f.2 hk
    refine ⟨⟨⟨s, hcard⟩, fun i => f.1 i.1⟩, ?_⟩
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ s
    · simp [fill, fillOn, hi]
    · have heq : f.1 i = base i := by
        by_contra hne
        exact hi (hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩))
      simp [fill, fillOn, hi, heq]
  calc
    Fintype.card {f : α → β // (changedSet base f).card ≤ k}
        ≤ Fintype.card (Σ s : {s : Finset α // s.card = k}, (s.1 → β)) :=
          Fintype.card_le_of_surjective fill hsurj
    _ = ∑ s : {s : Finset α // s.card = k}, Fintype.card β ^ k := by
      rw [Fintype.card_sigma]
      apply Finset.sum_congr rfl
      intro s _
      rw [Fintype.card_fun, Fintype.card_coe, s.2]
    _ = (Fintype.card α).choose k * Fintype.card β ^ k := by
      simp [Fintype.card_finset_len]

theorem card_sparse_endomaps_le (k : ℕ) (hk : k ≤ Fintype.card α) :
    Fintype.card {f : α → α // (changedSet id f).card ≤ k} ≤
      Fintype.card α ^ (2 * k) := by
  calc
    Fintype.card {f : α → α // (changedSet id f).card ≤ k}
        ≤ (Fintype.card α).choose k * Fintype.card α ^ k := card_sparse_maps_le id k hk
    _ ≤ Fintype.card α ^ k * Fintype.card α ^ k :=
      Nat.mul_le_mul_right _ (Nat.choose_le_pow _ _)
    _ = Fintype.card α ^ (2 * k) := by rw [← pow_add]; congr 1; omega

section Representatives

variable {ι γ : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq γ]

def firstRepresentative (f : ι → γ) (i : ι) : ι :=
  (Finset.univ.filter (fun j => f j = f i)).min'
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩⟩

theorem value_firstRepresentative (f : ι → γ) (i : ι) :
    f (firstRepresentative f i) = f i := by
  exact (Finset.mem_filter.mp (Finset.min'_mem
    (Finset.univ.filter (fun j => f j = f i)) _)).2

theorem firstRepresentative_le (f : ι → γ) (i : ι) :
    firstRepresentative f i ≤ i := by
  exact Finset.min'_le (Finset.univ.filter (fun j => f j = f i)) i
    (Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩)

theorem firstRepresentative_eq_of_value_eq (f : ι → γ) {i j : ι}
    (h : f i = f j) : firstRepresentative f i = firstRepresentative f j := by
  unfold firstRepresentative
  simp only [h]

theorem firstRepresentative_eq_iff (f : ι → γ) (i j : ι) :
    firstRepresentative f i = firstRepresentative f j ↔ f i = f j := by
  constructor
  · intro h
    have hv := congrArg f h
    simpa only [value_firstRepresentative] using hv
  · exact firstRepresentative_eq_of_value_eq f

theorem firstRepresentative_idempotent (f : ι → γ) (i : ι) :
    firstRepresentative f (firstRepresentative f i) = firstRepresentative f i :=
  firstRepresentative_eq_of_value_eq f (value_firstRepresentative f i)

theorem representative_image_eq_fixed (f : ι → γ) :
    Finset.univ.image (firstRepresentative f) =
      Finset.univ.filter (fun i => firstRepresentative f i = i) := by
  ext i
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨j, rfl⟩
    exact firstRepresentative_idempotent f j
  · intro hi
    exact ⟨i, hi⟩

theorem card_representative_image (f : ι → γ) :
    (Finset.univ.image (firstRepresentative f)).card = (Finset.univ.image f).card := by
  apply Finset.card_bij (fun i _ => f i)
  · intro i _
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  · intro i hi j hj hij
    have hri : firstRepresentative f i = i := by
      rw [representative_image_eq_fixed] at hi
      exact (Finset.mem_filter.mp hi).2
    have hrj : firstRepresentative f j = j := by
      rw [representative_image_eq_fixed] at hj
      exact (Finset.mem_filter.mp hj).2
    rw [← hri, ← hrj]
    exact firstRepresentative_eq_of_value_eq f hij
  · intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    refine ⟨firstRepresentative f i, Finset.mem_image.mpr
      ⟨i, Finset.mem_univ i, rfl⟩, value_firstRepresentative f i⟩

theorem card_changed_firstRepresentative (f : ι → γ) :
    (changedSet id (firstRepresentative f)).card =
      Fintype.card ι - (Finset.univ.image f).card := by
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun i => firstRepresentative f i ≠ i)
  have hfixed : (Finset.univ.filter (fun i => firstRepresentative f i = i)).card =
      (Finset.univ.image f).card := by
    rw [← representative_image_eq_fixed]
    exact card_representative_image f
  simp only [not_not, Finset.card_univ] at hpartition
  simp only [changedSet, id_eq]
  omega

theorem firstRepresentative_eq_of_same_equalities {δ : Type*} [DecidableEq δ]
    (f : ι → γ) (g : ι → δ)
    (h : ∀ i j, f i = f j ↔ g i = g j) :
    firstRepresentative f = firstRepresentative g := by
  funext i
  have hs : Finset.univ.filter (fun j => f j = f i) =
      Finset.univ.filter (fun j => g j = g i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, h]
  unfold firstRepresentative
  congr 1

abbrev CanonicalPattern (ι : Type*) [Fintype ι] [LinearOrder ι] (κ : ℕ) :=
  {r : ι → ι // (∀ i, r i ≤ i ∧ r (r i) = r i) ∧ (changedSet id r).card = κ}

theorem exists_canonical_pattern (f : ι → γ) (κ : ℕ)
    (hκ : Fintype.card ι - (Finset.univ.image f).card = κ) :
    ∃ r : CanonicalPattern ι κ, ∀ i j, r.1 i = r.1 j ↔ f i = f j := by
  refine ⟨⟨firstRepresentative f, ?_⟩, firstRepresentative_eq_iff f⟩
  constructor
  · exact fun i => ⟨firstRepresentative_le f i, firstRepresentative_idempotent f i⟩
  · exact (card_changed_firstRepresentative f).trans hκ

theorem card_canonical_patterns_le (κ : ℕ) (hκ : κ ≤ Fintype.card ι) :
    Nat.card (CanonicalPattern ι κ) ≤ Fintype.card ι ^ (2 * κ) := by
  rw [Nat.card_eq_fintype_card]
  let forget : CanonicalPattern ι κ →
      {r : ι → ι // (changedSet id r).card ≤ κ} :=
    fun r => ⟨r.1, Nat.le_of_eq r.2.2⟩
  have hinj : Function.Injective forget := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : {r : ι → ι // (changedSet id r).card ≤ κ} => z.1) hab
  exact (Fintype.card_le_of_injective forget hinj).trans (card_sparse_endomaps_le κ hκ)

theorem card_four_point_patterns_le (b κ : ℕ) (hb : 1 ≤ b) (hκ : κ ≤ 2) :
    Nat.card (CanonicalPattern (Fin (4 * b)) κ) ≤ (4 * b) ^ 4 := by
  have hκn : κ ≤ Fintype.card (Fin (4 * b)) := by simp; omega
  have h := card_canonical_patterns_le (ι := Fin (4 * b)) κ hκn
  simp only [Fintype.card_fin] at h
  apply h.trans
  exact Nat.pow_le_pow_right (by omega) (by omega)

end Representatives

end
end Balanced.ReusePatternCounting

end OAI
