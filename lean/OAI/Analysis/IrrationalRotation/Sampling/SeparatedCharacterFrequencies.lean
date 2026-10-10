import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Tactic

namespace OAI

namespace Invariant233
namespace SeparatedCharacterFrequencies

open scoped BigOperators
open Finset

theorem sum_ne_zero_of_prefix_domination (v : ℕ → ℤ) (q : ℕ → ℝ) (H : ℝ)
    (m : ℕ) (hq : ∀ i < m, 0 < q i)
    (hbound : ∀ i < m, |(v i : ℝ)| ≤ H)
    (hdom : ∀ k < m, H * (∑ i ∈ range k, q i) < q k)
    (hv : ∃ i < m, v i ≠ 0) :
    (∑ i ∈ range m, (v i : ℝ) * q i) ≠ 0 := by
  induction m with
  | zero => simp at hv
  | succ m ih =>
    by_cases hvm : v m = 0
    · have hv' : ∃ i < m, v i ≠ 0 := by
        obtain ⟨i, hi, hvi⟩ := hv
        refine ⟨i, ?_, hvi⟩
        by_contra h
        have : i = m := by omega
        subst i
        exact hvi hvm
      simpa [sum_range_succ, hvm] using
        ih (fun i hi => hq i (by omega)) (fun i hi => hbound i (by omega))
          (fun k hk => hdom k (by omega)) hv'
    · have hm : m < m + 1 := Nat.lt_succ_self m
      have hpre : |∑ i ∈ range m, (v i : ℝ) * q i| ≤ H * ∑ i ∈ range m, q i := by
        calc
          |∑ i ∈ range m, (v i : ℝ) * q i| ≤
              ∑ i ∈ range m, |(v i : ℝ) * q i| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ i ∈ range m, H * q i := by
            apply sum_le_sum
            intro i hi
            have hi' : i < m + 1 := by simpa using (lt_trans (mem_range.mp hi) hm)
            rw [abs_mul, abs_of_pos (hq i hi')]
            exact mul_le_mul_of_nonneg_right (hbound i hi') (hq i hi').le
          _ = H * ∑ i ∈ range m, q i := (mul_sum _ _ _).symm
      have hvpos : (0 : ℤ) < |v m| := abs_pos.mpr hvm
      have hvone : (1 : ℤ) ≤ |v m| := by omega
      have hvone' : (1 : ℝ) ≤ |(v m : ℝ)| := by exact_mod_cast hvone
      have hlast : q m ≤ |(v m : ℝ) * q m| := by
        rw [abs_mul, abs_of_pos (hq m hm)]
        nlinarith [hq m hm]
      intro hzero
      rw [sum_range_succ] at hzero
      have heq : (∑ i ∈ range m, (v i : ℝ) * q i) = -((v m : ℝ) * q m) := by
        linarith
      have habs : |∑ i ∈ range m, (v i : ℝ) * q i| = |(v m : ℝ) * q m| := by
        rw [heq, abs_neg]
      have hstrict := hdom m hm
      linarith

theorem prefix_domination_of_relative_gaps (q : ℕ → ℝ) (H : ℝ) (m : ℕ)
    (hH : 0 ≤ H) (hq : ∀ i, 0 < q i) (hmono : Monotone q)
    (hgap : ∀ i, i + 1 < m → (H * (m : ℝ)) * q i < q (i + 1)) :
    ∀ k < m, H * (∑ i ∈ range k, q i) < q k := by
  intro k hk
  cases k with
  | zero => simpa using hq 0
  | succ l =>
    have hsum : (∑ i ∈ range (l + 1), q i) ≤ (l + 1 : ℕ) * q l := by
      calc
        (∑ i ∈ range (l + 1), q i) ≤ ∑ _i ∈ range (l + 1), q l := by
          apply sum_le_sum
          intro i hi
          exact hmono (by simpa using mem_range.mp hi)
        _ = (l + 1 : ℕ) * q l := by simp
    have hlm : ((l + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk.le
    calc
      H * (∑ i ∈ range (l + 1), q i) ≤ H * (((l + 1 : ℕ) : ℝ) * q l) :=
        mul_le_mul_of_nonneg_left hsum hH
      _ ≤ H * ((m : ℝ) * q l) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hlm (hq l).le) hH
      _ = (H * (m : ℝ)) * q l := by ring
      _ < q (l + 1) := hgap l hk

theorem fourier_zsmul (v q : ℤ) (x : AddCircle (1 : ℝ)) :
    fourier v (q • x) = fourier (v * q) x := by
  simp only [fourier_apply, mul_zsmul]

theorem product_fourier_characters (v q : ℕ → ℤ) (m : ℕ) (x : AddCircle (1 : ℝ)) :
    (∏ i ∈ range m, fourier (v i) (q i • x)) =
      fourier (∑ i ∈ range m, v i * q i) x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, sum_range_succ, ih, fourier_add, fourier_zsmul]

theorem integral_fourier_eq_zero {k : ℤ} (hk : k ≠ 0) :
    (∫ x : AddCircle (1 : ℝ), fourier k x) = 0 := by
  exact MeasureTheory.integral_eq_zero_of_add_right_eq_neg
    (fourier_add_half_inv_index hk (by norm_num))

theorem integral_product_fourier_eq_zero (v q : ℕ → ℤ) (m : ℕ)
    (hfreq : (∑ i ∈ range m, v i * q i) ≠ 0) :
    (∫ x : AddCircle (1 : ℝ), ∏ i ∈ range m, fourier (v i) (q i • x)) = 0 := by
  simp_rw [product_fourier_characters]
  exact integral_fourier_eq_zero hfreq

theorem eventually_nonzero_frequency (v : ℕ → ℤ) (q : ℕ → ℕ → ℕ) (m : ℕ)
    (hq : ∀ j i, 0 < q j i) (hmono : ∀ j, Monotone (q j))
    (hgap : ∀ i, i + 1 < m → Filter.Tendsto
      (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) Filter.atTop Filter.atTop)
    (hv : ∃ i < m, v i ≠ 0) :
    ∀ᶠ j in Filter.atTop, (∑ i ∈ range m, v i * (q j i : ℤ)) ≠ 0 := by
  let H : ℝ := ∑ i ∈ range m, |(v i : ℝ)|
  have hH : 0 ≤ H := sum_nonneg (fun _ _ => abs_nonneg _)
  have hbound : ∀ i < m, |(v i : ℝ)| ≤ H := by
    intro i hi
    change |(v i : ℝ)| ≤ ∑ k ∈ range m, |(v k : ℝ)|
    exact single_le_sum (fun k _ => abs_nonneg (v k : ℝ)) (mem_range.mpr hi)
  have hgaps : ∀ᶠ j in Filter.atTop, ∀ i ∈ range m,
      i + 1 < m → (H * (m : ℝ)) * (q j i : ℝ) < (q j (i + 1) : ℝ) := by
    rw [Finset.eventually_all]
    intro i hi
    by_cases him : i + 1 < m
    · filter_upwards [(hgap i him).eventually_gt_atTop (H * (m : ℝ))] with j hj
      intro _
      exact (lt_div_iff₀ (by exact_mod_cast hq j i)).mp hj
    · exact Filter.Eventually.of_forall (fun _ h => (him h).elim)
  filter_upwards [hgaps] with j hj
  have hqreal : ∀ i, (0 : ℝ) < q j i := fun i => by exact_mod_cast hq j i
  have hmonoreal : Monotone (fun i => (q j i : ℝ)) := by
    intro a b hab
    change (q j a : ℝ) ≤ (q j b : ℝ)
    exact_mod_cast hmono j hab
  have hdom := prefix_domination_of_relative_gaps (fun i => (q j i : ℝ)) H m
    hH hqreal hmonoreal (fun i hi => hj i (mem_range.mpr (by omega)) hi)
  have hreal := sum_ne_zero_of_prefix_domination v (fun i => (q j i : ℝ)) H m
    (fun i _ => hqreal i) hbound hdom hv
  exact_mod_cast hreal

theorem eventually_integral_product_fourier_eq_zero
    (v : ℕ → ℤ) (q : ℕ → ℕ → ℕ) (m : ℕ)
    (hq : ∀ j i, 0 < q j i) (hmono : ∀ j, Monotone (q j))
    (hgap : ∀ i, i + 1 < m → Filter.Tendsto
      (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) Filter.atTop Filter.atTop)
    (hv : ∃ i < m, v i ≠ 0) :
    ∀ᶠ j in Filter.atTop,
      (∫ x : AddCircle (1 : ℝ), ∏ i ∈ range m, fourier (v i) ((q j i : ℤ) • x)) = 0 := by
  filter_upwards [eventually_nonzero_frequency v q m hq hmono hgap hv] with j hj
  exact integral_product_fourier_eq_zero v (fun i => (q j i : ℤ)) m hj

end SeparatedCharacterFrequencies
end Invariant233

end OAI
