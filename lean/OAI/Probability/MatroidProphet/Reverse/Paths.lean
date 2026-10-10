import OAI.Probability.MatroidProphet.Density.Guarded

namespace OAI

namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]

noncomputable def reversePrefix (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) : ℕ → Set α
  | 0 => if k < 0 then M.closure ∅ else univ
  | h+1 => M.closure (densityEnabled M hE κ (D h) (activation h) k
      (reversePrefix M hE κ D C S k h) ∪ (C h ∩ S h))

noncomputable def reverseNominal (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) (h : ℕ) : Set α :=
  densityEnabled M hE κ (D h) (activation h) k (reversePrefix M hE κ D C S k h)

lemma reversePrefix_succ (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) (h : ℕ) :
    reversePrefix M hE κ D C S k (h+1) =
      M.closure (reverseNominal M hE κ D C S k h ∪ (C h ∩ S h)) := rfl

lemma reversePrefix_agrees (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (k : ℤ) (h : ℕ) :
    reversePrefix M hE κ D C (fun j => nominalPath M hE κ D C j (k+1)) k h =
      guardedPath M hE κ D C h k := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [reversePrefix, ih]
    rfl

lemma reverseNominal_agrees (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (k : ℤ) (h : ℕ) :
    reverseNominal M hE κ D C (fun j => nominalPath M hE κ D C j (k+1)) k h =
      nominalPath M hE κ D C h k := by
  rw [reverseNominal, reversePrefix_agrees]
  rfl

lemma reversePrefix_mono (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C C' S S' : ℕ → Set α) {k k' : ℤ} (hkk' : k ≤ k')
    (hC : ∀ j, C j ⊆ C' j) (hS : ∀ j, S j ⊆ S' j) (h : ℕ) :
    reversePrefix M hE κ D C S k h ⊆ reversePrefix M hE κ D C' S' k' h := by
  induction h with
  | zero => exact guardedPath_mono M hE κ D C 0 hkk'
  | succ h ih =>
    exact M.closure_subset_closure
      (union_subset_union (densityEnabled_mono M hE κ (D h) (activation h) hkk' ih)
        (inter_subset_inter (hC h) (hS h)))

lemma reverseNominal_mono (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C C' S S' : ℕ → Set α) {k k' : ℤ} (hkk' : k ≤ k')
    (hC : ∀ j, C j ⊆ C' j) (hS : ∀ j, S j ⊆ S' j) (h : ℕ) :
    reverseNominal M hE κ D C S k h ⊆ reverseNominal M hE κ D C' S' k' h :=
  densityEnabled_mono M hE κ (D h) (activation h) hkk'
    (reversePrefix_mono M hE κ D C C' S S' hkk' hC hS h)

lemma reversePrefix_congr_before (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C C' S S' : ℕ → Set α) (k : ℤ) (h : ℕ)
    (hC : ∀ j < h, C j = C' j) (hS : ∀ j < h, S j = S' j) :
    reversePrefix M hE κ D C S k h = reversePrefix M hE κ D C' S' k h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [reversePrefix, reversePrefix, ih (fun j hj => hC j (by omega))
      (fun j hj => hS j (by omega)), hC h (by omega), hS h (by omega)]

lemma reverseNominal_congr_before (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C C' S S' : ℕ → Set α) (k : ℤ) (h : ℕ)
    (hC : ∀ j < h, C j = C' j) (hS : ∀ j < h, S j = S' j) :
    reverseNominal M hE κ D C S k h = reverseNominal M hE κ D C' S' k h := by
  rw [reverseNominal, reverseNominal, reversePrefix_congr_before M hE κ D C C' S S' k h hC hS]

lemma reversePrefix_subset_later (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C C' : ℕ → Set α) (k : ℤ) (h : ℕ) :
    reversePrefix M hE κ D C' (fun j => nominalPath M hE κ D C j (k+1)) k h ⊆
      guardedPath M hE κ D C h (k+1) := by
  induction h with
  | zero => exact guardedPath_mono M hE κ D C 0 (by omega)
  | succ h ih =>
    have hn := densityEnabled_mono M hE κ (D h) (activation h) (by omega : k ≤ k+1) ih
    have hs : reversePrefix M hE κ D C' (fun j => nominalPath M hE κ D C j (k+1)) k (h+1) ⊆
        nominalPath M hE κ D C h (k+1) := by
      exact (M.closure_subset_closure (union_subset hn inter_subset_right)).trans_eq
        (nominalPath_flat M hE κ D C h (k+1)).closure
    exact hs.trans (nominal_subset_guarded M hE κ D C h (k+1))

lemma reverseNominal_subset_later (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C C' : ℕ → Set α) (k : ℤ) (h : ℕ) :
    reverseNominal M hE κ D C' (fun j => nominalPath M hE κ D C j (k+1)) k h ⊆
      nominalPath M hE κ D C h (k+1) :=
  densityEnabled_mono M hE κ (D h) (activation h) (by omega)
    (reversePrefix_subset_later M hE κ D C C' k h)

lemma reversePrefix_subset_succ (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) (h : ℕ) :
    reversePrefix M hE κ D C S k h ⊆ reversePrefix M hE κ D C S k (h+1) :=
  (densityEnabled_extensive M hE κ (D h) (activation h) k _).trans
    (subset_union_left.trans (M.subset_closure _ (by simp [hE])))

omit [Fintype α] in
lemma union_inter_sdiff (N C S : Set α) : N ∪ (C ∩ (S \ N)) = N ∪ (C ∩ S) := by
  ext e
  change (e ∈ N ∨ (e ∈ C ∧ e ∈ S ∧ e ∉ N)) ↔ (e ∈ N ∨ (e ∈ C ∧ e ∈ S))
  tauto

noncomputable def departingGuards (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) (h : ℕ) : Set α :=
  C h ∩ (S h \ reverseNominal M hE κ D C S k h)

lemma reversePrefix_departing_only (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) (h : ℕ) :
    reversePrefix M hE κ D (departingGuards M hE κ D C S k) S k h =
      reversePrefix M hE κ D C S k h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [reversePrefix, reversePrefix, ih]
    change M.closure (reverseNominal M hE κ D C S k h ∪
        ((C h ∩ (S h \ reverseNominal M hE κ D C S k h)) ∩ S h)) = _
    have hi : (C h ∩ (S h \ reverseNominal M hE κ D C S k h)) ∩ S h =
        C h ∩ (S h \ reverseNominal M hE κ D C S k h) := inter_eq_self_of_subset_left (fun _ he => he.2.1)
    rw [hi, union_inter_sdiff]
    rfl

lemma reverseNominal_departing_only (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) (h : ℕ) :
    reverseNominal M hE κ D (departingGuards M hE κ D C S k) S k h =
      reverseNominal M hE κ D C S k h := by
  rw [reverseNominal, reverseNominal, reversePrefix_departing_only]

noncomputable def departureBatch (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C G : ℕ → Set α) (h : ℕ) (k : ℤ) : Set α :=
  G h ∩ (nominalPath M hE κ D C h (k+1) \ nominalPath M hE κ D C h k)

lemma departureBatch_disjoint_time (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C G : ℕ → Set α) (h : ℕ) {k l : ℤ} (hkl : k ≠ l) :
    Disjoint (departureBatch M hE κ D C G h k) (departureBatch M hE κ D C G h l) := by
  apply Set.disjoint_left.mpr
  intro e he hf
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · exact hf.2.2 (nominalPath_mono M hE κ D C h (by omega : k+1 ≤ l) he.2.1)
  · exact he.2.2 (nominalPath_mono M hE κ D C h (by omega : l+1 ≤ k) hf.2.1)

lemma departureBatch_disjoint_group (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C G : ℕ → Set α) {h j : ℕ} (hG : Disjoint (G h) (G j)) (k l : ℤ) :
    Disjoint (departureBatch M hE κ D C G h k) (departureBatch M hE κ D C G j l) :=
  hG.mono inter_subset_left inter_subset_left

noncomputable def hybridGuards (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C T : ℕ → Set α) (b : ℤ) (h : ℕ) : Set α :=
  (C h ∩ nominalPath M hE κ D C h (b-1)) ∪
    (T h ∩ (nominalPath M hE κ D C h b \ nominalPath M hE κ D C h (b-1)))

noncomputable def lowerCompetition (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C T : ℕ → Set α) (b : ℤ) : ℕ → Set α
  | 0 => ∅
  | h+1 => lowerCompetition M hE κ D C T b h ∪
      (T h ∩ (nominalPath M hE κ D C h b \ nominalPath M hE κ D C h (b-1)))

lemma hybridPrefix_contains (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C T : ℕ → Set α) (b : ℤ) (h : ℕ) :
    guardedPath M hE κ D C h (b-2) ∪ lowerCompetition M hE κ D C T b h ⊆
      reversePrefix M hE κ D (hybridGuards M hE κ D C T b)
        (fun j => nominalPath M hE κ D C j b) (b-1) h := by
  induction h with
  | zero =>
    exact union_subset (guardedPath_mono M hE κ D C 0 (by omega)) (empty_subset _)
  | succ h ih =>
    let A := reversePrefix M hE κ D (hybridGuards M hE κ D C T b)
      (fun j => nominalPath M hE κ D C j b) (b-1) h
    let N := reverseNominal M hE κ D (hybridGuards M hE κ D C T b)
      (fun j => nominalPath M hE κ D C j b) (b-1) h
    have hFn : nominalPath M hE κ D C h (b-2) ⊆ N :=
      densityEnabled_mono M hE κ (D h) (activation h) (by omega)
        (subset_union_left.trans ih)
    have hguards : C h ∩ nominalPath M hE κ D C h (b-1) ⊆
        hybridGuards M hE κ D C T b h ∩ nominalPath M hE κ D C h b := by
      intro e he
      exact ⟨Or.inl he, nominalPath_mono M hE κ D C h (by omega) he.2⟩
    have hF : guardedPath M hE κ D C (h+1) (b-2) ⊆
        reversePrefix M hE κ D (hybridGuards M hE κ D C T b)
          (fun j => nominalPath M hE κ D C j b) (b-1) (h+1) := by
      rw [guardedPath_succ, reversePrefix_succ]
      have ht : b-2+1 = b-1 := by omega
      rw [ht]
      exact M.closure_subset_closure (union_subset_union hFn hguards)
    apply union_subset hF
    change lowerCompetition M hE κ D C T b h ∪ _ ⊆ _
    apply union_subset
    · exact (subset_union_right.trans ih).trans
        (reversePrefix_subset_succ M hE κ D (hybridGuards M hE κ D C T b)
          (fun j => nominalPath M hE κ D C j b) (b-1) h)
    · intro e he
      apply M.subset_closure _ (by simp [hE])
      exact Or.inr ⟨Or.inr he, he.2.1⟩

lemma hybrid_containment (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C T : ℕ → Set α) (b : ℤ) (h : ℕ) (henabled : activation h ≤ b-1) :
    densityExpansion M hE κ (D h)
      (guardedPath M hE κ D C h (b-2) ∪ lowerCompetition M hE κ D C T b h) ⊆
      reverseNominal M hE κ D (hybridGuards M hE κ D C T b)
        (fun j => nominalPath M hE κ D C j b) (b-1) h := by
  rw [reverseNominal, densityEnabled, ite_eq_left henabled]
  exact densityExpansion_mono M hE κ (D h) (hybridPrefix_contains M hE κ D C T b h)

end MatroidProphet

end OAI
