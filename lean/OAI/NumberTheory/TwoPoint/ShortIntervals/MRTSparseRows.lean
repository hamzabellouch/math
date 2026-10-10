import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSparsePolynomial
import OAI.NumberTheory.TwoPoint.Fourier.MinorArcPacking

namespace OAI

/-! Summable Gram rows on one-separated heights.  A square-root frequency
remainder costs only the number of sampled heights, not the full interval. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_separated_cauchy_sum {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |x i-x j|) :
    (∑ i ∈ S, 1/(1+(x i)^2)) ≤ 8 := by
  let b := fun i => ⌊|x i|⌋₊
  let L := S.sup b
  let F := fun j => S.filter (fun i => b i = j)
  have hindex (i : ι) (hi : i ∈ S) : b i ≤ L := le_sup hi
  have hband (j : ℕ) (i : ι) (hi : i ∈ F j) :
      (j:ℝ) ≤ |x i| ∧ |x i| < (j:ℝ)+1 := by
    have he := (mem_filter.mp hi).2
    have hl := Nat.floor_le (abs_nonneg (x i))
    have hu := Nat.lt_floor_add_one |x i|
    change (b i:ℝ) ≤ |x i| at hl
    change |x i| < (b i:ℝ)+1 at hu
    rw [he] at hl hu
    exact ⟨hl,hu⟩
  have hcard (j : ℕ) : (F j).card ≤ 2 := by
    apply (card_le_card (s := F j) (t := S.filter
      (fun i => (j:ℝ) ≤ |x i| ∧ |x i| < (j:ℝ)+1)) ?_).trans
      (minor_arc_absolute_band_packing S x 1 j hsep)
    intro i hi
    exact mem_filter.mpr ⟨(mem_filter.mp hi).1, hband j i hi⟩
  have hpiece (j : ℕ) : (∑ i ∈ F j, 1/(1+(x i)^2)) ≤ 2/(1+(j:ℝ)^2) := by
    calc
      _ ≤ ∑ _i ∈ F j, 1/(1+(j:ℝ)^2) := by
        apply sum_le_sum
        intro i hi
        have hs := pow_le_pow_left₀ (Nat.cast_nonneg j) (hband j i hi).1 2
        rw [sq_abs] at hs
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      _ = ((F j).card:ℝ)/(1+(j:ℝ)^2) := by simp [div_eq_mul_inv]
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hcard j) (by positivity)
  have hpartition : (∑ i ∈ S, 1/(1+(x i)^2)) =
      ∑ j ∈ Icc 0 L, ∑ i ∈ F j, 1/(1+(x i)^2) := by
    symm
    exact sum_fiberwise_of_maps_to
      (fun i hi => mem_Icc.mpr ⟨Nat.zero_le _, hindex i hi⟩) _
  have hI : Icc 0 L = insert 0 (Ioc 0 L) := by
    ext j
    simp only [mem_Icc, mem_insert, mem_Ioc]
    omega
  have htail := mrt_quadratic_gap_sum (by norm_num : (0:ℝ)<1) L
  simp only [div_one] at htail
  rw [hpartition]
  apply (sum_le_sum (fun j _ => hpiece j)).trans
  rw [hI, sum_insert (by simp)]
  simp only [Nat.cast_zero, zero_pow (by omega : 2≠0), add_zero, div_one]
  have he : (∑ j ∈ Ioc 0 L, 2/(1+(j:ℝ)^2)) =
      2 * ∑ j ∈ Ioc 0 L, (1+(j:ℝ)^2)⁻¹ := by
    simp only [div_eq_mul_inv, mul_sum]
  rw [he]
  linarith

theorem mrt_sparse_weighted_row_energy {ι : Type*} (K : Finset ι)
    (w freq : ι → ℝ) (a : ι → ℂ) (hw : ∀ n ∈ K, 0 ≤ w n)
    (S : Finset ℝ) (hsep : ∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hkernel : ∀ t ∈ S, ∀ s ∈ S,
      ‖mrtExponentialPolynomial K (fun n => (w n:ℂ)) freq (t-s)‖ ≤
        A/(1+(t-s)^2)+D) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial K (fun n => (w n:ℂ)*a n) freq t‖^2) ≤
      (8*A+(S.card:ℝ)*D) * ∑ n ∈ K, w n*‖a n‖^2 := by
  apply mrt_sparse_weighted_polynomial_energy K w freq a hw S (by positivity)
  intro t ht
  have hc : (∑ s ∈ S, 1/(1+(t-s)^2)) ≤ 8 := by
    apply mrt_separated_cauchy_sum S (fun s => t-s)
    intro s hs u hu hsu
    simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using hsep s hs u hu hsu
  calc
    _ ≤ ∑ s ∈ S, (A/(1+(t-s)^2)+D) := sum_le_sum (fun s hs => hkernel t ht s hs)
    _ = A*(∑ s ∈ S, 1/(1+(t-s)^2))+(S.card:ℝ)*D := by
      simp only [sum_add_distrib, div_eq_mul_inv, mul_sum, sum_const, nsmul_eq_mul,
        one_mul]
    _ ≤ A*8+(S.card:ℝ)*D := add_le_add (mul_le_mul_of_nonneg_left hc hA) le_rfl
    _ = _ := by ring

end TwoPointCorrelations

end OAI
