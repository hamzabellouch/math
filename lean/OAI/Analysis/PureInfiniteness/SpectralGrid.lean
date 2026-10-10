import OAI.Analysis.WeakInfiniteness.SpectralWindows

namespace OAI

/-! A finite one-dimensional localization used in KR02 Remark 7.5.
The plateau overlap bound is independent of the size of the finite grid. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

def gridHat (k : ℤ) (x : ℝ) : ℝ := spectralTent k 1 x
def gridPlateau (k : ℤ) (x : ℝ) : ℝ := spectralPlateau k 1 x

lemma continuous_gridHat (k : ℤ) : Continuous (gridHat k) :=
  spectralTent_continuous k 1

lemma continuous_gridPlateau (k : ℤ) : Continuous (gridPlateau k) :=
  spectralPlateau_continuous k 1

lemma gridHat_nonneg (k : ℤ) (x : ℝ) : 0 ≤ gridHat k x :=
  spectralTent_nonneg k 1 x

lemma gridPlateau_bounds (k : ℤ) (x : ℝ) :
    0 ≤ gridPlateau k x ∧ gridPlateau k x ≤ 1 := by
  exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

lemma gridPlateau_mul_gridHat (k : ℤ) (x : ℝ) :
    gridPlateau k x * gridHat k x = gridHat k x := by
  by_cases h : |x - (k : ℝ)| ≤ 1
  · rw [show gridPlateau k x = 1 from spectralPlateau_one (by norm_num) h, one_mul]
  · have hz : gridHat k x = 0 := spectralTent_zero (by norm_num) (le_of_not_ge h)
    rw [hz, mul_zero]

lemma gridHat_floor (x : ℝ) : gridHat ⌊x⌋ x = (⌊x⌋ : ℝ) + 1 - x := by
  have hlo := Int.floor_le x
  have hhi := Int.lt_floor_add_one x
  unfold gridHat spectralTent
  rw [div_one, abs_of_nonneg (sub_nonneg.mpr hlo), max_eq_left (by linarith)]
  ring

lemma gridHat_floor_add_one (x : ℝ) : gridHat (⌊x⌋ + 1) x = x - (⌊x⌋ : ℝ) := by
  have hlo := Int.floor_le x
  have hhi := Int.lt_floor_add_one x
  unfold gridHat spectralTent
  rw [Int.cast_add, Int.cast_one, div_one,
    abs_of_nonpos (by linarith), max_eq_left (by linarith)]
  ring

lemma gridHat_eq_zero_off_floor (x : ℝ) (k : ℤ)
    (hk : k ≠ ⌊x⌋) (hk' : k ≠ ⌊x⌋ + 1) : gridHat k x = 0 := by
  apply spectralTent_zero (by norm_num)
  have hlo := Int.floor_le x
  have hhi := Int.lt_floor_add_one x
  rcases le_or_gt k ⌊x⌋ with h | h
  · have hi : k + 1 ≤ ⌊x⌋ := by omega
    have hi' : (k : ℝ) + 1 ≤ (⌊x⌋ : ℝ) := by exact_mod_cast hi
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hi : ⌊x⌋ + 2 ≤ k := by omega
    have hi' : (⌊x⌋ : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hi
    rw [abs_of_nonpos (by linarith)]
    linarith

lemma sum_gridHat_eq_one (a b : ℤ) (x : ℝ)
    (ha : (a : ℝ) ≤ x) (hb : x ≤ (b : ℝ)) :
    ∑ k ∈ Finset.Icc a (b + 1), gridHat k x = 1 := by
  classical
  have hnlo : a ≤ ⌊x⌋ := Int.le_floor.mpr ha
  have hnhi : ⌊x⌋ ≤ b := Int.floor_le_iff.mpr (by exact_mod_cast (by linarith : x < (b : ℝ) + 1))
  have hsub : {⌊x⌋, ⌊x⌋ + 1} ⊆ Finset.Icc a (b + 1) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> simp only [Finset.mem_Icc] <;> omega
  have he := Finset.sum_subset hsub (f := fun k => gridHat k x) (by
    intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    exact gridHat_eq_zero_off_floor x k hk.1 hk.2)
  rw [← he, Finset.sum_pair (by omega : ⌊x⌋ ≠ ⌊x⌋ + 1),
    gridHat_floor, gridHat_floor_add_one]
  ring

lemma gridPlateau_eq_zero_off_near_floor (x : ℝ) (k : ℤ)
    (hk : k ∉ Finset.Icc (⌊x⌋ - 2) (⌊x⌋ + 2)) : gridPlateau k x = 0 := by
  apply spectralPlateau_zero (by norm_num)
  have hlo := Int.floor_le x
  have hhi := Int.lt_floor_add_one x
  simp only [Finset.mem_Icc, not_and_or, not_le] at hk
  rcases hk with h | h
  · have hi : (k : ℝ) + 2 < (⌊x⌋ : ℝ) := by
      exact_mod_cast (show k + 2 < ⌊x⌋ by omega)
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hi : (⌊x⌋ : ℝ) + 2 < (k : ℝ) := by exact_mod_cast h
    have hi' : (⌊x⌋ : ℝ) + 3 ≤ (k : ℝ) := by exact_mod_cast (show ⌊x⌋ + 3 ≤ k by omega)
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- Uniform overlap: the estimate does not grow with the finite grid. -/
lemma sum_gridPlateau_le_five (s : Finset ℤ) (x : ℝ) :
    ∑ k ∈ s, gridPlateau k x ≤ 5 := by
  classical
  let t := s ∩ Finset.Icc (⌊x⌋ - 2) (⌊x⌋ + 2)
  have he := Finset.sum_subset (Finset.inter_subset_left : t ⊆ s)
    (f := fun k => gridPlateau k x) (by
      intro k hk hkt
      apply gridPlateau_eq_zero_off_near_floor x k
      intro hi
      exact hkt (Finset.mem_inter.mpr ⟨hk, hi⟩))
  rw [← he]
  calc
    _ ≤ ∑ _k ∈ t, (1 : ℝ) := Finset.sum_le_sum fun k _ => (gridPlateau_bounds k x).2
    _ = (t.card : ℝ) := by simp
    _ ≤ ((Finset.Icc (⌊x⌋ - 2) (⌊x⌋ + 2)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : t ⊆ _)
    _ = 5 := by
      rw [Int.card_Icc]
      have heq : ⌊x⌋ + 2 + 1 - (⌊x⌋ - 2) = 5 := by omega
      rw [heq]
      norm_num

end WeakPureInfiniteness

end

end OAI
