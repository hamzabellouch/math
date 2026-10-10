import OAI.Analysis.PureInfiniteness.SpectralGrid

namespace OAI

/-! Finite-dimensional product grids for the joint spectral localization in
KR02 Remark 7.5.  The overlap bound depends on the number of coordinates,
not on the mesh size or number of cells. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

lemma sum_gridHat_first_moment (a b : ℤ) (x : ℝ)
    (ha : (a : ℝ) ≤ x) (hb : x ≤ (b : ℝ)) :
    ∑ k ∈ Finset.Icc a (b + 1), (k : ℝ) * gridHat k x = x := by
  classical
  have hnlo : a ≤ ⌊x⌋ := Int.le_floor.mpr ha
  have hnhi : ⌊x⌋ ≤ b := Int.floor_le_iff.mpr
    (by exact_mod_cast (by linarith : x < (b : ℝ) + 1))
  have hsub : {⌊x⌋, ⌊x⌋ + 1} ⊆ Finset.Icc a (b + 1) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> simp only [Finset.mem_Icc] <;> omega
  have he := Finset.sum_subset hsub (f := fun (k : ℤ) => (k : ℝ) * gridHat k x) (by
    intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [gridHat_eq_zero_off_floor x k hk.1 hk.2, mul_zero])
  rw [← he, Finset.sum_pair (by omega : ⌊x⌋ ≠ ⌊x⌋ + 1),
    gridHat_floor, gridHat_floor_add_one, Int.cast_add, Int.cast_one]
  ring

variable {I : Type*} [Fintype I]

abbrev SpectralGridCell (s : I → Finset ℤ) := ∀ i, ↥(s i)

def productGridHat (s : I → Finset ℤ) (k : SpectralGridCell s) (x : I → ℝ) : ℝ :=
  ∏ i, gridHat (k i) (x i)

def productGridPlateau (s : I → Finset ℤ) (k : SpectralGridCell s) (x : I → ℝ) : ℝ :=
  ∏ i, gridPlateau (k i) (x i)

lemma productGridHat_nonneg (s : I → Finset ℤ) (k : SpectralGridCell s) (x : I → ℝ) :
    0 ≤ productGridHat s k x :=
  Finset.prod_nonneg fun i _ => gridHat_nonneg (k i) (x i)

lemma productGridPlateau_bounds (s : I → Finset ℤ) (k : SpectralGridCell s) (x : I → ℝ) :
    0 ≤ productGridPlateau s k x ∧ productGridPlateau s k x ≤ 1 := by
  refine ⟨Finset.prod_nonneg (fun i _ => (gridPlateau_bounds (k i) (x i)).1), ?_⟩
  exact Finset.prod_le_one₀ (fun i _ => (gridPlateau_bounds (k i) (x i)).1)
    (fun i _ => (gridPlateau_bounds (k i) (x i)).2)

lemma productGridPlateau_mul_hat (s : I → Finset ℤ) (k : SpectralGridCell s) (x : I → ℝ) :
    productGridPlateau s k x * productGridHat s k x = productGridHat s k x := by
  unfold productGridPlateau productGridHat
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => gridPlateau_mul_gridHat (k i) (x i)

lemma continuous_productGridHat (s : I → Finset ℤ) (k : SpectralGridCell s) :
    Continuous (productGridHat s k) := by
  unfold productGridHat
  exact continuous_finsetProd _ fun i _ => (continuous_gridHat (k i)).comp (continuous_apply i)

lemma continuous_productGridPlateau (s : I → Finset ℤ) (k : SpectralGridCell s) :
    Continuous (productGridPlateau s k) := by
  unfold productGridPlateau
  exact continuous_finsetProd _ fun i _ => (continuous_gridPlateau (k i)).comp (continuous_apply i)

variable [DecidableEq I]

lemma sum_productGridHat (s : I → Finset ℤ) (x : I → ℝ)
    (h : ∀ i, ∑ k ∈ s i, gridHat k (x i) = 1) :
    ∑ k : SpectralGridCell s, productGridHat s k x = 1 := by
  unfold productGridHat
  rw [← Fintype.prod_sum (fun i (j : ↥(s i)) => gridHat j (x i))]
  have hs (i : I) : ∑ k : ↥(s i), gridHat k (x i) = 1 := by
    exact (Finset.sum_coe_sort (s i) (fun k => gridHat k (x i))).trans (h i)
  simp only [hs, Finset.prod_const_one]

lemma sum_productGridPlateau_le (s : I → Finset ℤ) (x : I → ℝ) :
    ∑ k : SpectralGridCell s, productGridPlateau s k x ≤ (5 : ℝ) ^ Fintype.card I := by
  unfold productGridPlateau
  rw [← Fintype.prod_sum (fun i (j : ↥(s i)) => gridPlateau j (x i))]
  calc
    _ ≤ ∏ _i : I, (5 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Finset.sum_nonneg fun k _ => (gridPlateau_bounds k (x i)).1
      · intro i _
        exact (Finset.sum_coe_sort (s i) (fun k => gridPlateau k (x i))).le.trans
          (sum_gridPlateau_le_five (s i) (x i))
    _ = _ := by simp

end WeakPureInfiniteness

end

end OAI
