import OAI.Analysis.TriangularHilbert.MaskedDissipation

namespace OAI

section
namespace TriangularHilbert
open MeasureTheory
open scoped BigOperators
noncomputable section

def sortedTimes (S : Finset ℝ) (hS : S.Nonempty) (k : ℕ) : ℝ :=
  S.orderEmbOfFin rfl ⟨min k (S.card-1),lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (Finset.card_pos.mpr hS) (by omega))⟩

lemma sortedTimes_monotone (S : Finset ℝ) (hS : S.Nonempty) : Monotone (sortedTimes S hS) := by
  intro k l hkl
  apply (S.orderEmbOfFin rfl).monotone
  exact min_le_min_right _ hkl

lemma sortedTimes_mem (S : Finset ℝ) (hS : S.Nonempty) (k : ℕ) : sortedTimes S hS k ∈ S :=
  Finset.orderEmbOfFin_mem _ _ _

lemma sortedTimes_zero (S : Finset ℝ) (hS : S.Nonempty) : sortedTimes S hS 0 = S.min' hS := by
  exact Finset.orderEmbOfFin_zero rfl (Finset.card_pos.mpr hS)

lemma sortedTimes_last (S : Finset ℝ) (hS : S.Nonempty) : sortedTimes S hS (S.card-1) = S.max' hS := by
  simp only [sortedTimes,min_self]
  exact Finset.orderEmbOfFin_last rfl (Finset.card_pos.mpr hS)

lemma sortedTimes_no_between (S : Finset ℝ) (hS : S.Nonempty) (k : ℕ) {e : ℝ}
    (he : e ∈ S) : ¬ (sortedTimes S hS k < e ∧ e < sortedTimes S hS (k+1)) := by
  have he' : e ∈ Set.range (S.orderEmbOfFin rfl) := by simpa using he
  obtain ⟨j,rfl⟩ := he'
  intro ⟨h1,h2⟩
  have h1' := (S.orderEmbOfFin rfl).lt_iff_lt.mp h1
  have h2' := (S.orderEmbOfFin rfl).lt_iff_lt.mp h2
  change min k (S.card-1) < j.val at h1'
  change j.val < min (k+1) (S.card-1) at h2'
  omega

lemma sortedTimes_le_iff (S : Finset ℝ) (hS : S.Nonempty) (k : ℕ) {e s : ℝ}
    (he : e ∈ S) (hs : s ∈ Set.Ico (sortedTimes S hS k) (sortedTimes S hS (k+1))) :
    e ≤ s ↔ e ≤ sortedTimes S hS k := by
  constructor
  · intro hes
    by_contra h
    exact sortedTimes_no_between S hS k he ⟨lt_of_not_ge h,hes.trans_lt hs.2⟩
  · exact fun h => h.trans hs.1

lemma sortedTimes_mask_const (S : Finset ℝ) (hS : S.Nonempty) (k : ℕ) {a b s : ℝ}
    (ha : a ∈ S) (hb : b ∈ S)
    (hs : s ∈ Set.Ico (sortedTimes S hS k) (sortedTimes S hS (k+1))) (A : ℂ) :
    windowMask a b s A = windowMask a b (sortedTimes S hS k) A := by
  have h1 := sortedTimes_le_iff S hS k ha hs
  have h2 := not_congr (sortedTimes_le_iff S hS k hb hs)
  simp only [not_le] at h2
  simp only [windowMask,h1,h2]

lemma intervalIntegrable_of_Ico_eq {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (he : ∀ s ∈ Set.Ico a b, f s=g s) :
    IntervalIntegrable f volume a b := by
  apply hg.congr_ae
  rw [Set.uIoc_of_le hab]
  apply (ae_restrict_iff' measurableSet_Ioc).2
  filter_upwards [volume.ae_ne b] with s hsb hs
  exact (he s ⟨hs.1.le,lt_of_le_of_ne hs.2 hsb⟩).symm

end
end TriangularHilbert
end

end OAI
