import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

/-!
# The monotone-variation step in the shell reconstruction

The proof of the manuscript's `asm:monotone-shell` uses summable positive
measure increments ζₙ = αₙ − αₙ₊₁. After interchanging a finite sum of
Fourier bands with these increments, the correction is
`∑' n, (Q (min n M) - Qbase) (ζ n)`. It converges in any Banach
space by the uniform bounds for the low-pass operators.
No rate of convergence of αₙ to α∞ is required.
-/

namespace Falconer
open Filter
open scoped Topology

/-- Positive increments of a decreasing, nonnegative sequence are summable.
For the shell lemma, `m n` is the total mass of `α n`. -/
theorem summable_antitone_mass_increments (m : ℕ → ℝ)
    (hm : Antitone m) (hpos : ∀ n, 0 ≤ m n) :
    Summable (fun n => m n - m (n + 1)) := by
  apply summable_of_sum_range_le (fun n => sub_nonneg.mpr (hm (Nat.le_succ n)))
    (c := m 0)
  intro N
  have he : ∑ n ∈ Finset.range N, (m n - m (n + 1)) = m 0 - m N := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; ring
  rw [he]
  exact sub_le_self _ (hpos N)

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
private theorem lowpass_difference_bound (Q : ℕ → E →L[ℝ] F)
    (Qbase : E →L[ℝ] F) {C : ℝ} (hQ : ∀ n, ‖Q n‖ ≤ C) (hbase : ‖Qbase‖ ≤ C)
    (z : E) (n : ℕ) : ‖(Q n - Qbase) z‖ ≤ (2 * C) * ‖z‖ := by
  calc
    ‖(Q n - Qbase) z‖ ≤ ‖Q n - Qbase‖ * ‖z‖ := (Q n - Qbase).le_opNorm z
    _ ≤ (‖Q n‖ + ‖Qbase‖) * ‖z‖ :=
      mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
    _ ≤ (2 * C) * ‖z‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      linarith [hQ n]

omit [CompleteSpace F] in
/-- Finite telescoping of the low-pass differences at one fixed increment. -/
theorem sum_bands_before_increment (Q : ℕ → E →L[ℝ] F) (z : E) (n M : ℕ) :
    (∑ j ∈ Finset.range M, if j ≤ n then (Q (j + 1) - Q j) z else 0) =
      (Q (min (n + 1) M) - Q 0) z := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : M ≤ n
    · rw [ite_eq_left h, min_eq_right (by omega), min_eq_right (by omega)]
      simp only [sub_apply]
      abel
    · rw [ite_eq_right h, min_eq_left (by omega), min_eq_left (by omega), add_zero]

omit [CompleteSpace F] in
/-- The finite-band identity of the monotone shell argument. The outer band
sum is finite; the inner increment sum is absolutely convergent. -/
theorem finite_band_variation_identity [CompleteSpace E]
    (Q : ℕ → E →L[ℝ] F) (z : ℕ → E)
    (hz : Summable (fun n => ‖z n‖)) (M : ℕ) :
    (∑ j ∈ Finset.range M,
      (Q (j + 1) - Q j) (∑' n, if j ≤ n then z n else 0)) =
    ∑' n, (Q (min (n + 1) M) - Q 0) (z n) := by
  classical
  have ht (j : ℕ) : Summable (fun n => if j ≤ n then z n else 0) := by
    apply hz.of_norm_bounded
    intro n
    split_ifs <;> simp
  calc
    _ = ∑ j ∈ Finset.range M, ∑' n,
        (Q (j + 1) - Q j) (if j ≤ n then z n else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (Q (j + 1) - Q j).map_tsum (ht j)
    _ = ∑' n, ∑ j ∈ Finset.range M,
        (Q (j + 1) - Q j) (if j ≤ n then z n else 0) :=
      (Summable.tsum_finsetSum (fun j _ => (Q (j + 1) - Q j).summable (ht j))).symm
    _ = _ := by
      apply tsum_congr
      intro n
      simpa only [apply_ite, map_zero] using sum_bands_before_increment Q (z n) n M

/-- Absolute convergence of the variation correction from summable increments. -/
theorem summable_lowpass_variation (Q : ℕ → E →L[ℝ] F) (Qbase : E →L[ℝ] F)
    {C : ℝ} (hQ : ∀ n, ‖Q n‖ ≤ C) (hbase : ‖Qbase‖ ≤ C)
    (z : ℕ → E) (hz : Summable (fun n => ‖z n‖)) :
    Summable (fun n => (Q n - Qbase) (z n)) := by
  exact (hz.mul_left (2 * C)).of_norm_bounded
    (fun n => lowpass_difference_bound Q Qbase hQ hbase (z n) n)

/-- The triangular partial corrections converge in norm. This is precisely the
limit used after the finite-band identity in `asm:variation-tail`. -/
theorem truncated_lowpass_variation_tendsto
    (Q : ℕ → E →L[ℝ] F) (Qbase : E →L[ℝ] F)
    {C : ℝ} (hQ : ∀ n, ‖Q n‖ ≤ C) (hbase : ‖Qbase‖ ≤ C)
    (z : ℕ → E) (hz : Summable (fun n => ‖z n‖)) :
    Tendsto (fun M : ℕ => ∑' n, (Q (min n M) - Qbase) (z n)) atTop
      (𝓝 (∑' n, (Q n - Qbase) (z n))) := by
  apply tendsto_tsum_of_dominated_convergence (hz.mul_left (2 * C))
  · intro n
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with M hM
    rw [min_eq_left hM]
  · exact Eventually.of_forall (fun M n =>
      lowpass_difference_bound Q Qbase hQ hbase (z n) (min n M))

/-- The finite sum of bands applied to the decreasing tails has a norm limit,
with no quantitative assumption on the rate at which those tails vanish. -/
theorem finite_band_variation_tendsto [CompleteSpace E]
    (Q : ℕ → E →L[ℝ] F) {C : ℝ} (hQ : ∀ n, ‖Q n‖ ≤ C)
    (z : ℕ → E) (hz : Summable (fun n => ‖z n‖)) :
    Tendsto (fun M => ∑ j ∈ Finset.range M,
      (Q (j + 1) - Q j) (∑' n, if j ≤ n then z n else 0)) atTop
      (𝓝 (∑' n, (Q (n + 1) - Q 0) (z n))) := by
  simp_rw [finite_band_variation_identity Q z hz]
  apply tendsto_tsum_of_dominated_convergence (hz.mul_left (2 * C))
  · intro n
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (n + 1)] with M hM
    rw [min_eq_left hM]
  · exact Eventually.of_forall (fun M n =>
      lowpass_difference_bound Q (Q 0) hQ (hQ 0) (z n) (min (n + 1) M))

end
end Falconer

end OAI
