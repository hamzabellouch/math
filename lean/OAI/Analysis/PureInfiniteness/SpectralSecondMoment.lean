import OAI.Analysis.PureInfiniteness.JointSpectralEstimates

namespace OAI

/-! The second-moment estimate for the finite spectral return map. It controls
its Schwarz defect on a sampled selfadjoint coordinate. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

lemma sum_gridHat_second_moment (a b : ℤ) (x : ℝ)
    (ha : (a : ℝ) ≤ x) (hb : x ≤ (b : ℝ)) :
    ∑ k ∈ Finset.Icc a (b + 1), (k : ℝ) ^ 2 * gridHat k x =
      x ^ 2 + (x - ⌊x⌋) * (⌊x⌋ + 1 - x) := by
  classical
  have hnlo : a ≤ ⌊x⌋ := Int.le_floor.mpr ha
  have hnhi : ⌊x⌋ ≤ b := Int.floor_le_iff.mpr (by linarith)
  have hsub : {⌊x⌋, ⌊x⌋ + 1} ⊆ Finset.Icc a (b + 1) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> simp only [Finset.mem_Icc] <;> omega
  have he := Finset.sum_subset hsub (f := fun k : ℤ => (k : ℝ) ^ 2 * gridHat k x) (by
    intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [gridHat_eq_zero_off_floor x k hk.1 hk.2, mul_zero])
  rw [← he, Finset.sum_pair (by omega : ⌊x⌋ ≠ ⌊x⌋ + 1),
    gridHat_floor, gridHat_floor_add_one, Int.cast_add, Int.cast_one]
  ring

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma sum_productGridHat_weighted_coordinate (s : I → Finset ℤ) (x : I → ℝ) (i : I)
    (w : ℤ → ℝ) (hpart : ∀ j, ∑ k ∈ s j, gridHat k (x j) = 1) :
    ∑ k : SpectralGridCell s, w (k i) * productGridHat s k x =
      ∑ k ∈ s i, w k * gridHat k (x i) := by
  classical
  have hf (k : SpectralGridCell s) :
      w (k i) * productGridHat s k x =
      ∏ j, ((if j = i then w (k j) else 1) * gridHat (k j) (x j)) := by
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']
    rfl
  simp_rw [hf]
  rw [← Fintype.prod_sum (fun j (k : ↥(s j)) =>
    (if j = i then w k else 1) * gridHat k (x j))]
  have hs (j : I) :
      (∑ k : ↥(s j), (if j = i then w k else 1) * gridHat k (x j)) =
      if j = i then (∑ k ∈ s i, w k * gridHat k (x i)) else 1 := by
    by_cases hji : j = i
    · subst j
      simp only [ite_true]
      exact Finset.sum_coe_sort (s i) (fun k : ℤ => w k * gridHat k (x i))
    · simp only [hji, ite_false, one_mul]
      exact (Finset.sum_coe_sort (s j) (fun k : ℤ => gridHat k (x j))).trans (hpart j)
  simp_rw [hs]
  exact Fintype.prod_ite_eq' i _

lemma joint_spectral_retained_second_moment (s : I → Finset ℤ) (x : I → ℝ) (i : I)
    (hp : ∀ j, ∑ k ∈ s j, gridHat k (x j) = 1)
    (hm : ∑ k ∈ s i, (k : ℝ) ^ 2 * gridHat k (x i) =
      (x i) ^ 2 + (x i - ⌊x i⌋) * (⌊x i⌋ + 1 - x i))
    (hpos : ∀ j k, k ∈ s j → (0 : ℤ) ≤ k) :
    |(x i) ^ 2 - ∑ k : SpectralGridCell s
      with retainedSpectralCell s k, (k i : ℝ) ^ 2 * productGridHat s k x| ≤ 1 := by
  classical
  have hfull : (∑ k : SpectralGridCell s, (k i : ℝ) ^ 2 * productGridHat s k x) =
      (x i) ^ 2 + (x i - ⌊x i⌋) * (⌊x i⌋ + 1 - x i) := by
    rw [sum_productGridHat_weighted_coordinate s x i (fun k => (k : ℝ) ^ 2) hp]
    exact hm
  have homit0 : 0 ≤ ∑ k : SpectralGridCell s with ¬ retainedSpectralCell s k,
      (k i : ℝ) ^ 2 * productGridHat s k x :=
    Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (productGridHat_nonneg _ _ _)
  have homit1 : (∑ k : SpectralGridCell s with ¬ retainedSpectralCell s k,
      (k i : ℝ) ^ 2 * productGridHat s k x) ≤ 1 := by
    calc
      _ ≤ ∑ k : SpectralGridCell s with ¬ retainedSpectralCell s k, productGridHat s k x := by
        apply Finset.sum_le_sum
        intro k hk
        have hk0 : (0 : ℤ) ≤ k i := hpos i (k i) (k i).property
        have hk1 : (k i : ℤ) ≤ 1 := by
          have h := (Finset.mem_filter.mp hk).2
          by_contra h'
          exact h ⟨i, by omega⟩
        have hki0 : (0 : ℝ) ≤ (k i : ℤ) := by exact_mod_cast hk0
        have hki1 : (k i : ℝ) ≤ 1 := by exact_mod_cast hk1
        apply mul_le_of_le_one_left (productGridHat_nonneg _ _ _)
        nlinarith
      _ ≤ ∑ k : SpectralGridCell s, productGridHat s k x :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun k _ _ => productGridHat_nonneg _ _ _)
      _ = 1 := sum_productGridHat s x hp
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := retainedSpectralCell s) (f := fun k => (k i : ℝ) ^ 2 * productGridHat s k x)
  rw [hfull] at hsplit
  have hlo := Int.floor_le (x i)
  have hhi := Int.lt_floor_add_one (x i)
  have hv0 : 0 ≤ (x i - ⌊x i⌋) * (⌊x i⌋ + 1 - x i) := mul_nonneg (by linarith) (by linarith)
  have hv1 : (x i - ⌊x i⌋) * (⌊x i⌋ + 1 - x i) ≤ 1 := by nlinarith [sq_nonneg (x i - ⌊x i⌋)]
  apply abs_le.mpr
  constructor <;> linarith

end WeakPureInfiniteness

end

end OAI
