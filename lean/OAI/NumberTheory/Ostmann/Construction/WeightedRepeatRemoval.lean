import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order
import OAI.NumberTheory.Ostmann.Construction.RepeatRemovalPointwise
import OAI.NumberTheory.Ostmann.Preliminaries.WeightedMomentShift

namespace OAI

/-! # Removing repeated primes inside the positive amplified moment -/

namespace Ostmann

open scoped BigOperators Classical

/-- A pointwise square-root shift controls the error in the weighted moment.
All quantities on the right are the actual unperturbed moments. -/
theorem weighted_power_approximation {ι : Type*} (w f D : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) (b : ℝ) (hb : 0 ≤ b)
    (k : ℕ) (hk : 0 < k) (hws : Summable w)
    (hfs : Summable (fun i => w i * f i ^ k))
    (hD : ∀ i, |D i - f i ^ k| ≤ (f i + b) ^ k - f i ^ k) :
    Summable (fun i => w i * D i) ∧
      |(∑' i, w i * D i) - (∑' i, w i * f i ^ k)| ≤
        ((∑' i, w i * f i ^ k) ^ (1 / (k : ℝ)) +
          b * (∑' i, w i) ^ (1 / (k : ℝ))) ^ k - (∑' i, w i * f i ^ k) := by
  obtain ⟨hs, hbnd⟩ := weighted_moment_shift w f hw hf b hb k hk hws hfs
  have hp (i : ι) : ‖w i * (D i - f i ^ k)‖ ≤
      w i * (f i + b) ^ k - w i * f i ^ k := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw i), ← mul_sub]
    exact mul_le_mul_of_nonneg_left (hD i) (hw i)
  have hen : Summable (fun i => ‖w i * (D i - f i ^ k)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp (hs.sub hfs)
  have he : Summable (fun i => w i * (D i - f i ^ k)) :=
    Summable.of_norm_bounded (hs.sub hfs) hp
  have hd : Summable (fun i => w i * D i) := by
    simpa only [mul_sub, sub_add_cancel] using he.add hfs
  refine ⟨hd, ?_⟩
  calc
    |(∑' i, w i * D i) - (∑' i, w i * f i ^ k)| =
        ‖∑' i, w i * (D i - f i ^ k)‖ := by rw [← hd.tsum_sub hfs]; simp only [mul_sub, Real.norm_eq_abs]
    _ ≤ ∑' i, ‖w i * (D i - f i ^ k)‖ := norm_tsum_le_tsum_norm hen
    _ ≤ ∑' i, (w i * (f i + b) ^ k - w i * f i ^ k) :=
      hen.tsum_le_tsum hp (hs.sub hfs)
    _ = (∑' i, w i * (f i + b) ^ k) - (∑' i, w i * f i ^ k) := hs.tsum_sub hfs
    _ ≤ _ := sub_le_sub_right hbnd _

noncomputable def ternaryMean {A : Type*} [Fintype A] (y : A → ℝ) : ℝ :=
  (∑ i, y i) / Fintype.card A

noncomputable def ternaryDistinctMean {A : Type*} [Fintype A] (y : A → ℝ) (k : ℕ) : ℝ :=
  (∑ e : Fin k ↪ A, ∏ i, y (e i)) / (Fintype.card A : ℝ) ^ k

theorem ternaryMean_abs_le_one {A : Type*} [Fintype A]
    (y : A → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1 ∨ y i = -1) :
    |ternaryMean y| ≤ 1 := by
  by_cases hA : Fintype.card A = 0
  · simp [ternaryMean, hA]
  have hJ : (0 : ℝ) < Fintype.card A := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hA)
  rw [ternaryMean, abs_div, abs_of_pos hJ, div_le_one hJ]
  calc
    |∑ i, y i| ≤ ∑ i, |y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : A, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rcases hy i with h | h | h <;> simp [h]
    _ = _ := by simp

/-- Actual distinct-index averaging, with no assumed repeat-removal estimate. -/
theorem weighted_ternary_distinct_moment {ι A : Type*} [Fintype A] [DecidableEq A]
    (w : ι → ℝ) (y : ι → A → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hy : ∀ i a, y i a = 0 ∨ y i a = 1 ∨ y i a = -1)
    (k : ℕ) (hk : 0 < k) (heven : Even k) (hkA : k ≤ Fintype.card A)
    (hws : Summable w) :
    Summable (fun i => w i * ternaryDistinctMean (y i) k) ∧
      |(∑' i, w i * ternaryDistinctMean (y i) k) -
          (∑' i, w i * ternaryMean (y i) ^ k)| ≤
        ((∑' i, w i * ternaryMean (y i) ^ k) ^ (1 / (k : ℝ)) +
          (Real.sqrt ((k : ℝ) * Fintype.card A) / Fintype.card A) *
            (∑' i, w i) ^ (1 / (k : ℝ))) ^ k -
          (∑' i, w i * ternaryMean (y i) ^ k) := by
  have hA : 0 < Fintype.card A := lt_of_lt_of_le hk hkA
  have hf (i : ι) : |ternaryMean (y i)| ^ k ≤ 1 :=
    pow_le_one₀ (abs_nonneg _) (ternaryMean_abs_le_one (y i) (hy i))
  have hfs : Summable (fun i => w i * |ternaryMean (y i)| ^ k) := by
    apply Summable.of_nonneg_of_le (fun i => mul_nonneg (hw i) (pow_nonneg (abs_nonneg _) _))
      (fun i => ?_) hws
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf i) (hw i)
  have hh := weighted_power_approximation w (fun i => |ternaryMean (y i)|)
    (fun i => ternaryDistinctMean (y i) k) hw (fun _ => abs_nonneg _)
    (Real.sqrt ((k : ℝ) * Fintype.card A) / Fintype.card A) (by positivity)
    k hk hws hfs (fun i => by
      simpa only [ternaryDistinctMean, ternaryMean, heven.pow_abs] using
        normalized_ternary_distinct_product_error (y i) (hy i) k hkA hA)
  simpa only [heven.pow_abs] using hh

end Ostmann

end OAI
