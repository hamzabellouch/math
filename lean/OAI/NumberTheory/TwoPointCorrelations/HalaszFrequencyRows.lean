import OAI.NumberTheory.TwoPointCorrelations.HalaszWeightedMeanSquare

namespace OAI

/-! A local frequency-mass estimate controls the entire quadratic-decay row.
This keeps the prime-counting input separate from the finite harmonic-analysis
argument, and applies to the actual finite Dirichlet polynomial. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped BigOperators Classical

noncomputable def halaszFrequencyShell {ι : Type*} (S : Finset ι)
    (freq : ι → ℝ) (T u : ℝ) (k : ℕ) : Finset ι :=
  S.filter (fun i => Nat.floor (T * |freq i - u|) = k)

lemma halasz_quadratic_kernel_sum (M : ℕ) :
    (∑ k ∈ range (M + 1), (1 + (k : ℝ) ^ 2)⁻¹) ≤ 4 := by
  have he : range (M + 1) = insert 0 (Ioc 0 M) := by
    ext k
    simp only [mem_range, mem_insert, mem_Ioc]
    omega
  rw [he, sum_insert (by simp)]
  have hh := mrt_quadratic_gap_sum (R := 1) (by norm_num) M
  norm_num only [div_one] at hh
  norm_num only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), add_zero, inv_one]
  linarith

/-- Shell mass at frequency resolution `1/T` controls the whole Fourier
kernel row, uniformly in the number and placement of the frequencies. -/
theorem halasz_frequency_row_of_shells {ι : Type*} (S : Finset ι)
    (freq w : ι → ℝ) (u : ℝ) {T B : ℝ} (hT : 0 < T) (hB : 0 ≤ B)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hshell : ∀ k : ℕ, ∑ i ∈ halaszFrequencyShell S freq T u k, w i ≤ B / T) :
    (∑ i ∈ S, w i * (2 * T / (1 + T ^ 2 * (freq i - u) ^ 2))) ≤ 8 * B := by
  classical
  let bin : ι → ℕ := fun i => Nat.floor (T * |freq i - u|)
  let M := S.sup bin
  have hmaps : ∀ i ∈ S, bin i ∈ range (M + 1) := by
    intro i hi
    exact mem_range.mpr (Nat.lt_succ_of_le (le_sup (f := bin) hi))
  have hpoint (i : ι) :
      2 * T / (1 + T ^ 2 * (freq i - u) ^ 2) ≤
        2 * T * (1 + (bin i : ℝ) ^ 2)⁻¹ := by
    have hfloor : (bin i : ℝ) ≤ T * |freq i - u| :=
      Nat.floor_le (mul_nonneg hT.le (abs_nonneg _))
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (bin i)) hfloor 2
    rw [mul_pow, sq_abs] at hsq
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact inv_anti₀ (by positivity) (add_le_add le_rfl hsq)
  have hgroup : (∑ i ∈ S, w i * (2 * T * (1 + (bin i : ℝ) ^ 2)⁻¹)) =
      ∑ k ∈ range (M + 1), (2 * T * (1 + (k : ℝ) ^ 2)⁻¹) *
        ∑ i ∈ halaszFrequencyShell S freq T u k, w i := by
    rw [← sum_fiberwise_of_maps_to hmaps]
    apply sum_congr rfl
    intro k _
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    have he := (mem_filter.mp hi).2
    change bin i = k at he
    rw [he]
    ring
  calc
    _ ≤ ∑ i ∈ S, w i * (2 * T * (1 + (bin i : ℝ) ^ 2)⁻¹) := by
      exact sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hpoint i) (hw i hi))
    _ = _ := hgroup
    _ ≤ ∑ k ∈ range (M + 1), (2 * T * (1 + (k : ℝ) ^ 2)⁻¹) * (B / T) := by
      exact sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hshell k) (by positivity))
    _ = 2 * B * ∑ k ∈ range (M + 1), (1 + (k : ℝ) ^ 2)⁻¹ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      field_simp
    _ ≤ 2 * B * 4 :=
      mul_le_mul_of_nonneg_left (halasz_quadratic_kernel_sum M) (by positivity)
    _ = _ := by ring

/-- The corresponding mean-square estimate for a finite polynomial whose
weighted frequency shells all have controlled mass. -/
theorem halasz_mean_square_of_frequency_shells {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (w freq : ι → ℝ) {T B : ℝ} (hT : 0 < T) (hB : 0 ≤ B)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hshell : ∀ i ∈ S, ∀ k : ℕ,
      ∑ j ∈ halaszFrequencyShell S freq T (freq i) k, w j ≤ B / T) :
    (∫ t in -T..T,
      ‖mrtExponentialPolynomial S (fun i => a i * (w i : ℂ)) freq t‖ ^ 2) ≤
      8 * Real.exp 1 * B * ∑ i ∈ S, ‖a i‖ ^ 2 * w i := by
  have hrow : ∀ i ∈ S,
      ∑ j ∈ S, w j * (2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2)) ≤ 8 * B := by
    intro i hi
    convert halasz_frequency_row_of_shells S freq w (freq i) hT hB hw (hshell i hi) using 1
    apply sum_congr rfl
    intro j _
    rw [show (freq i - freq j) ^ 2 = (freq j - freq i) ^ 2 by ring]
  apply (halasz_mean_square_of_weighted_rows S a w freq hT hw hrow).trans_eq
  ring


/-- A shell is the union of its two one-sided frequency intervals. -/
lemma halasz_shell_mass_of_windows {ι : Type*} (S : Finset ι)
    (freq w : ι → ℝ) (u : ℝ) {T A : ℝ} (hT : 0 < T)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hwindow : ∀ v : ℝ,
      (∑ i ∈ S.filter (fun i => v ≤ freq i ∧ freq i ≤ v + 1 / T), w i) ≤ A / T)
    (k : ℕ) :
    (∑ i ∈ halaszFrequencyShell S freq T u k, w i) ≤ 2 * A / T := by
  classical
  let Q := halaszFrequencyShell S freq T u k
  let R := Q.filter (fun i => u ≤ freq i)
  let L := Q.filter (fun i => ¬u ≤ freq i)
  have he : Q = R ∪ L := by
    ext i
    simp only [R, L, mem_union, mem_filter]
    tauto
  have hd : Disjoint R L := by
    rw [disjoint_left]
    intro i hi hj
    exact (mem_filter.mp hj).2 (mem_filter.mp hi).2
  have hgap (i : ι) (hi : i ∈ Q) :
      (k : ℝ) / T ≤ |freq i - u| ∧ |freq i - u| ≤ ((k : ℝ) + 1) / T := by
    have heq := (mem_filter.mp hi).2
    change Nat.floor (T * |freq i - u|) = k at heq
    have hlo := Nat.floor_le (mul_nonneg hT.le (abs_nonneg (freq i - u)))
    have hhi := Nat.lt_floor_add_one (T * |freq i - u|)
    rw [heq] at hlo hhi
    constructor
    · exact (div_le_iff₀ hT).mpr (by linarith)
    · exact (le_div_iff₀ hT).mpr (by linarith)
  have hR : R ⊆ S.filter (fun i =>
      u + (k : ℝ) / T ≤ freq i ∧ freq i ≤ u + (k : ℝ) / T + 1 / T) := by
    intro i hi
    obtain ⟨hiQ, hiu⟩ := mem_filter.mp hi
    have hg := hgap i hiQ
    rw [abs_of_nonneg (sub_nonneg.mpr hiu)] at hg
    refine mem_filter.mpr ⟨(mem_filter.mp hiQ).1, ?_⟩
    simp only [add_div] at hg ⊢
    constructor <;> linarith
  have hL : L ⊆ S.filter (fun i =>
      u - ((k : ℝ) + 1) / T ≤ freq i ∧
        freq i ≤ u - ((k : ℝ) + 1) / T + 1 / T) := by
    intro i hi
    obtain ⟨hiQ, hiu⟩ := mem_filter.mp hi
    have hg := hgap i hiQ
    rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge hiu))] at hg
    refine mem_filter.mpr ⟨(mem_filter.mp hiQ).1, ?_⟩
    simp only [add_div] at hg ⊢
    constructor <;> linarith
  have hbR : (∑ i ∈ R, w i) ≤ A / T := by
    apply (sum_le_sum_of_subset_of_nonneg hR ?_).trans (hwindow _)
    intro i hi _
    exact hw i (mem_filter.mp hi).1
  have hbL : (∑ i ∈ L, w i) ≤ A / T := by
    apply (sum_le_sum_of_subset_of_nonneg hL ?_).trans (hwindow _)
    intro i hi _
    exact hw i (mem_filter.mp hi).1
  change (∑ i ∈ Q, w i) ≤ _
  rw [he, sum_union hd]
  calc
    _ ≤ A / T + A / T := add_le_add hbR hbL
    _ = _ := by ring

/-- A uniform local frequency-mass bound gives a uniform kernel-row bound. -/
theorem halasz_frequency_row_of_windows {ι : Type*} (S : Finset ι)
    (freq w : ι → ℝ) (u : ℝ) {T A : ℝ} (hT : 0 < T) (hA : 0 ≤ A)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hwindow : ∀ v : ℝ,
      (∑ i ∈ S.filter (fun i => v ≤ freq i ∧ freq i ≤ v + 1 / T), w i) ≤ A / T) :
    (∑ i ∈ S, w i * (2 * T / (1 + T ^ 2 * (freq i - u) ^ 2))) ≤ 16 * A := by
  have hh := halasz_frequency_row_of_shells S freq w u hT (mul_nonneg (by norm_num) hA)
    hw (halasz_shell_mass_of_windows S freq w u hT hw hwindow)
  convert hh using 1; ring

end TwoPointCorrelations

end OAI
