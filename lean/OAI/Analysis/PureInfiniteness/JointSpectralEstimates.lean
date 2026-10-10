import OAI.Analysis.PureInfiniteness.SpectralProductGrid

namespace OAI

/-! The finite scalar estimates behind the joint nonunital spectral partition.
Cells touching the joint origin are omitted; the resulting first-moment error
is bounded independently of the number of cells. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

lemma gridHat_le_one (k : ℤ) (x : ℝ) : gridHat k x ≤ 1 := by
  unfold gridHat spectralTent
  rw [div_one]
  exact max_le (by linarith [abs_nonneg (x - (k : ℝ))]) zero_le_one

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma productGridHat_le_one (s : I → Finset ℤ) (k : SpectralGridCell s) (x : I → ℝ) :
    productGridHat s k x ≤ 1 :=
  Finset.prod_le_one₀ (fun i _ => gridHat_nonneg (k i) (x i)) (fun i _ => gridHat_le_one (k i) (x i))

lemma sum_productGridHat_first_moment (s : I → Finset ℤ) (x : I → ℝ) (i : I)
    (hpart : ∀ j, ∑ k ∈ s j, gridHat k (x j) = 1)
    (hmoment : ∑ k ∈ s i, (k : ℝ) * gridHat k (x i) = x i) :
    ∑ k : SpectralGridCell s, (k i : ℝ) * productGridHat s k x = x i := by
  classical
  have hf (k : SpectralGridCell s) :
      (k i : ℝ) * productGridHat s k x =
      ∏ j, ((if j = i then (k j : ℝ) else 1) * gridHat (k j) (x j)) := by
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']
    rfl
  simp_rw [hf]
  rw [← Fintype.prod_sum (fun j (k : ↥(s j)) =>
    (if j = i then (k : ℝ) else 1) * gridHat k (x j))]
  have hs (j : I) :
      (∑ k : ↥(s j), (if j = i then (k : ℝ) else 1) * gridHat k (x j)) =
      if j = i then x i else 1 := by
    by_cases hji : j = i
    · subst j
      simp only [ite_true]
      exact (Finset.sum_coe_sort (s i) (fun k : ℤ => (k : ℝ) * gridHat k (x i))).trans hmoment
    · simp only [hji, ite_false, one_mul]
      exact (Finset.sum_coe_sort (s j) (fun k => gridHat k (x j))).trans (hpart j)
  simp_rw [hs]
  exact Fintype.prod_ite_eq' i (fun _ => x i)

/-- A retained cell has a coordinate at least two lattice units from zero. -/
def retainedSpectralCell (s : I → Finset ℤ) (k : SpectralGridCell s) : Prop :=
  ∃ i, 2 ≤ (k i : ℤ)

instance (s : I → Finset ℤ) (k : SpectralGridCell s) : Decidable (retainedSpectralCell s k) :=
  inferInstanceAs (Decidable (∃ i, 2 ≤ (k i : ℤ)))

omit [DecidableEq I] in
lemma productGridPlateau_zero_at_origin (s : I → Finset ℤ) (k : SpectralGridCell s)
    (hk : retainedSpectralCell s k) : productGridPlateau s k 0 = 0 := by
  obtain ⟨i, hi⟩ := hk
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  change gridPlateau (k i) 0 = 0
  apply spectralPlateau_zero (by norm_num)
  have hik : (2 : ℝ) ≤ (k i : ℤ) := by exact_mod_cast hi
  simpa only [zero_sub, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (k i : ℤ)), mul_one] using hik

lemma joint_spectral_omitted_moment (s : I → Finset ℤ) (x : I → ℝ) (i : I)
    (hpart : ∀ j, ∑ k ∈ s j, gridHat k (x j) = 1)
    (hindices : ∀ j k, k ∈ s j → 0 ≤ k) :
    0 ≤ ∑ k : SpectralGridCell s with ¬ retainedSpectralCell s k,
      (k i : ℝ) * productGridHat s k x ∧
    (∑ k : SpectralGridCell s with ¬ retainedSpectralCell s k,
      (k i : ℝ) * productGridHat s k x) ≤ 1 := by
  classical
  constructor
  · apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (by exact_mod_cast hindices i (k i) (k i).property)
      (productGridHat_nonneg s k x)
  · calc
      _ ≤ ∑ k : SpectralGridCell s with ¬ retainedSpectralCell s k,
          productGridHat s k x := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' : ¬ retainedSpectralCell s k := (Finset.mem_filter.mp hk).2
        have hki : (k i : ℤ) ≤ 1 := by
          by_contra h
          exact hk' ⟨i, by omega⟩
        exact mul_le_of_le_one_left (productGridHat_nonneg s k x) (by exact_mod_cast hki)
      _ ≤ ∑ k : SpectralGridCell s, productGridHat s k x :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun k _ _ => productGridHat_nonneg s k x)
      _ = 1 := sum_productGridHat s x hpart

lemma joint_spectral_retained_moment (s : I → Finset ℤ) (x : I → ℝ) (i : I)
    (hpart : ∀ j, ∑ k ∈ s j, gridHat k (x j) = 1)
    (hmoment : ∑ k ∈ s i, (k : ℝ) * gridHat k (x i) = x i)
    (hindices : ∀ j k, k ∈ s j → 0 ≤ k) :
    |x i - ∑ k : SpectralGridCell s with retainedSpectralCell s k,
      (k i : ℝ) * productGridHat s k x| ≤ 1 := by
  classical
  have hs := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := retainedSpectralCell s)
    (f := fun k => (k i : ℝ) * productGridHat s k x)
  rw [sum_productGridHat_first_moment s x i hpart hmoment] at hs
  have he : x i - ∑ k : SpectralGridCell s with retainedSpectralCell s k,
      (k i : ℝ) * productGridHat s k x =
      ∑ k : SpectralGridCell s with ¬ retainedSpectralCell s k,
      (k i : ℝ) * productGridHat s k x := by linarith
  rw [he, abs_of_nonneg (joint_spectral_omitted_moment s x i hpart hindices).1]
  exact (joint_spectral_omitted_moment s x i hpart hindices).2

omit [DecidableEq I] in
lemma productGridPlateau_coordinate_sq_le (s : I → Finset ℤ)
    (k : SpectralGridCell s) (x : I → ℝ) (i : I) :
    (x i - (k i : ℝ)) ^ 2 * productGridPlateau s k x ≤
      4 * productGridPlateau s k x := by
  by_cases h : |x i - (k i : ℝ)| < 2
  · have hsq : (x i - (k i : ℝ)) ^ 2 ≤ 4 := by
      rw [abs_lt] at h
      nlinarith
    exact mul_le_mul_of_nonneg_right hsq (productGridPlateau_bounds s k x).1
  · have hz : gridPlateau (k i) (x i) = 0 :=
      spectralPlateau_zero (by norm_num) (by simpa only [mul_one] using le_of_not_gt h)
    have hp : productGridPlateau s k x = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hz
    rw [hp, mul_zero, mul_zero]

lemma sum_productGridPlateau_coordinate_sq_le (s : I → Finset ℤ)
    (x : I → ℝ) (i : I) (T : Finset (SpectralGridCell s)) :
    (∑ k ∈ T, (x i - (k i : ℝ)) ^ 2 * productGridPlateau s k x) ≤
      4 * (5 : ℝ) ^ Fintype.card I := by
  calc
    _ ≤ ∑ k ∈ T, 4 * productGridPlateau s k x :=
      Finset.sum_le_sum fun k _ => productGridPlateau_coordinate_sq_le s k x i
    _ = 4 * ∑ k ∈ T, productGridPlateau s k x := (Finset.mul_sum ..).symm
    _ ≤ 4 * ∑ k : SpectralGridCell s, productGridPlateau s k x := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
        (fun k _ _ => (productGridPlateau_bounds s k x).1)
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_productGridPlateau_le s x) (by norm_num)

end WeakPureInfiniteness

end

end OAI
