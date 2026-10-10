import OAI.Probability.MatroidProphet.Density.Path

namespace OAI

namespace MatroidProphet
open Set
variable {α : Type*} [Fintype α]

noncomputable def densityEnabled (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D : Set α) (a k : ℤ) (P : Set α) : Set α :=
  if a ≤ k then densityExpansion M hE κ D P else P

lemma densityEnabled_extensive (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D : Set α) (a k : ℤ) (P : Set α) :
    P ⊆ densityEnabled M hE κ D a k P := by
  by_cases hak : a ≤ k
  · simpa only [densityEnabled, ite_eq_left hak] using densityExpansion_extensive M hE κ D P
  · simp only [densityEnabled, ite_eq_right hak, Subset.rfl]

lemma densityEnabled_flat (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D : Set α) (a k : ℤ) {P : Set α} (hP : M.IsFlat P) :
    M.IsFlat (densityEnabled M hE κ D a k P) := by
  by_cases hak : a ≤ k
  · simpa only [densityEnabled, ite_eq_left hak] using densityExpansion_flat M hE κ D P
  · simpa only [densityEnabled, ite_eq_right hak] using hP

lemma densityEnabled_mono (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D : Set α) (a : ℤ) {k k' : ℤ} {P P' : Set α}
    (hkk' : k ≤ k') (hPP' : P ⊆ P') :
    densityEnabled M hE κ D a k P ⊆ densityEnabled M hE κ D a k' P' := by
  by_cases hak : a ≤ k
  · have hak' := hak.trans hkk'
    simpa only [densityEnabled, ite_eq_left hak, ite_eq_left hak'] using
      densityExpansion_mono M hE κ D hPP'
  · by_cases hak' : a ≤ k'
    · simpa only [densityEnabled, ite_eq_right hak, ite_eq_left hak'] using
        hPP'.trans (densityExpansion_extensive M hE κ D P')
    · simpa only [densityEnabled, ite_eq_right hak, ite_eq_right hak'] using hPP'

lemma densityEnabled_univ (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D : Set α) (a k : ℤ) : densityEnabled M hE κ D a k univ = univ :=
  Set.eq_univ_of_univ_subset (densityEnabled_extensive M hE κ D a k univ)

def activation (h : ℕ) : ℤ := -3 * ((h : ℤ) + 1)

noncomputable def guardedPath (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) : ℕ → ℤ → Set α
  | 0, k => if k < 0 then M.closure ∅ else univ
  | h + 1, k =>
      M.closure (densityEnabled M hE κ (D h) (activation h) k
          (guardedPath M hE κ D C h k) ∪
        (C h ∩ densityEnabled M hE κ (D h) (activation h) (k + 1)
          (guardedPath M hE κ D C h (k + 1))))

noncomputable def nominalPath (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (k : ℤ) : Set α :=
  densityEnabled M hE κ (D h) (activation h) k (guardedPath M hE κ D C h k)

lemma guardedPath_succ (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (k : ℤ) :
    guardedPath M hE κ D C (h+1) k =
      M.closure (nominalPath M hE κ D C h k ∪ (C h ∩ nominalPath M hE κ D C h (k+1))) := rfl

lemma guardedPath_flat (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (k : ℤ) :
    M.IsFlat (guardedPath M hE κ D C h k) := by
  cases h with
  | zero =>
    by_cases hk : k < 0
    · simpa only [guardedPath, ite_eq_left hk] using Matroid.isFlat_closure (M := M) ∅
    · simpa only [guardedPath, ite_eq_right hk, ← hE] using M.ground_isFlat
  | succ h => exact Matroid.isFlat_closure (M := M) _

lemma nominalPath_flat (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (k : ℤ) :
    M.IsFlat (nominalPath M hE κ D C h k) :=
  densityEnabled_flat M hE κ (D h) (activation h) k (guardedPath_flat M hE κ D C h k)

lemma guardedPath_mono (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) : Monotone (guardedPath M hE κ D C h) := by
  induction h with
  | zero =>
    intro i j hij
    by_cases hi : i < 0
    · by_cases hj : j < 0
      · simp only [guardedPath, ite_eq_left hi, ite_eq_left hj, Subset.rfl]
      · simp only [guardedPath, ite_eq_left hi, ite_eq_right hj, subset_univ]
    · have hj : ¬ j < 0 := by omega
      simp only [guardedPath, ite_eq_right hi, ite_eq_right hj, Subset.rfl]
  | succ h ih =>
    intro i j hij
    apply M.closure_subset_closure
    exact union_subset_union (densityEnabled_mono M hE κ (D h) (activation h) hij (ih hij))
      (inter_subset_inter_right (C h)
        (densityEnabled_mono M hE κ (D h) (activation h) (by omega) (ih (by omega))))

lemma nominalPath_mono (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) : Monotone (nominalPath M hE κ D C h) := by
  intro i j hij
  exact densityEnabled_mono M hE κ (D h) (activation h) hij
    (guardedPath_mono M hE κ D C h hij)

lemma guarded_subset_nominal (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (k : ℤ) :
    guardedPath M hE κ D C h k ⊆ nominalPath M hE κ D C h k :=
  densityEnabled_extensive M hE κ (D h) (activation h) k _

lemma nominal_subset_guarded (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (k : ℤ) :
    nominalPath M hE κ D C h k ⊆ guardedPath M hE κ D C (h+1) k :=
  subset_union_left.trans (M.subset_closure _ (by simp [hE]))

lemma guarded_subset_next_nominal (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) (k : ℤ) :
    guardedPath M hE κ D C (h+1) k ⊆ nominalPath M hE κ D C h (k+1) := by
  have hs : nominalPath M hE κ D C h k ∪ (C h ∩ nominalPath M hE κ D C h (k+1)) ⊆
      nominalPath M hE κ D C h (k+1) :=
    union_subset (nominalPath_mono M hE κ D C h (by omega)) inter_subset_right
  exact (M.closure_subset_closure hs).trans_eq (nominalPath_flat M hE κ D C h (k+1)).closure

lemma guardedPath_nonnegative (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) {k : ℤ} (hk : 0 ≤ k) :
    guardedPath M hE κ D C h k = univ := by
  induction h generalizing k with
  | zero => simp [guardedPath, not_lt_of_ge hk]
  | succ h ih =>
    rw [guardedPath, ih hk, ih (by omega), densityEnabled_univ, densityEnabled_univ]
    simp [hE]

lemma nominalPath_nonnegative (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) {k : ℤ} (hk : 0 ≤ k) :
    nominalPath M hE κ D C h k = univ := by
  rw [nominalPath, guardedPath_nonnegative M hE κ D C h hk, densityEnabled_univ]

lemma guardedPath_early (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) {k : ℤ} (hk : k < -3 * (h : ℤ) - 1) :
    guardedPath M hE κ D C h k = M.closure ∅ := by
  induction h generalizing k with
  | zero =>
    have hk' : k < 0 := by omega
    simp [guardedPath, hk']
  | succ h ih =>
    have hka : ¬ activation h ≤ k := by dsimp [activation]; push_cast at hk; omega
    have hk'a : ¬ activation h ≤ k+1 := by dsimp [activation]; push_cast at hk; omega
    have hkold : k < -3 * (h : ℤ) - 1 := by push_cast at hk; omega
    have hk'old : k+1 < -3 * (h : ℤ) - 1 := by omega
    rw [guardedPath, densityEnabled, densityEnabled, ite_eq_right hka, ite_eq_right hk'a,
      ih hkold, ih hk'old]
    rw [union_eq_self_of_subset_right inter_subset_right, M.closure_closure]

lemma nominalPath_early (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) {k : ℤ} (hk : k < activation h) :
    nominalPath M hE κ D C h k = M.closure ∅ := by
  rw [nominalPath, densityEnabled, ite_eq_right (not_le_of_gt hk)]
  apply guardedPath_early
  dsimp [activation] at hk
  omega

lemma nominalPath_baseline (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) :
    nominalPath M hE κ D C h (activation h) =
      densityExpansion M hE κ (D h) (M.closure ∅) := by
  rw [nominalPath, densityEnabled, ite_eq_left le_rfl, guardedPath_early]
  dsimp [activation]
  omega

lemma nominalPath_baseline_gap (M : Matroid α) (hE : M.E = univ)
    (κ : ℕ) (D C : ℕ → Set α) (h : ℕ) :
    nominalPath M hE κ D C h (activation h + 1) =
      nominalPath M hE κ D C h (activation h) := by
  rw [nominalPath_baseline, nominalPath, densityEnabled, ite_eq_left (by omega), guardedPath_early]
  dsimp [activation]
  omega

end MatroidProphet

end OAI
