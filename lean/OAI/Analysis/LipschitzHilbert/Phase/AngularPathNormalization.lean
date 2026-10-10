import OAI.Analysis.LipschitzHilbert.Phase.AngularSourceWeight

namespace OAI

/-! The equal-coordinate value of the shared analytic family. The
endpoint mass cancels exactly and leaves only parent-to-boundary ratios. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

/-- The path product in the shared analytic family is the exponential
weight used in the full-root variation estimate. -/
theorem hierarchyWeight_eq_path_product (n b : ℕ → ℝ) (phase : ℕ → ℂ)
    (a : ℝ) (N : ℕ) (hn : 0 < n N)
    (hn' : ∀ j < N, 0 < n (j+1)) (hb : ∀ j < N, 0 < b j) :
    hierarchyWeight n (fun j => Real.log (b j / n (j+1))) phase a N =
      ((n N ^ (-a) : ℝ) : ℂ) * ∏ j ∈ Finset.range N,
        Complex.exp (phase j * (Real.log (n (j+1) / b j) : ℂ)) := by
  have hpow : ((n N ^ (-a) : ℝ) : ℂ) =
      Complex.exp ((-a * Real.log (n N) : ℝ) : ℂ) := by
    rw [Real.rpow_def_of_pos hn, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hpow, ← Complex.exp_sum, ← Complex.exp_add, hierarchyWeight, hierarchyLog]
  congr 1
  have hsum : (∑ j ∈ Finset.range N, phase j * (Real.log (n (j+1) / b j) : ℂ)) =
      -(∑ j ∈ Finset.range N, phase j * (Real.log (b j / n (j+1)) : ℂ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjN := Finset.mem_range.mp hj
    rw [Real.log_div (hn' j hjN).ne' (hb j hjN).ne',
      Real.log_div (hb j hjN).ne' (hn' j hjN).ne']
    push_cast
    ring
  rw [hsum]
  ring

theorem normalized_endpoint_telescope (n b : ℕ → ℝ) (a : ℝ) (N : ℕ)
    (hn : ∀ j ≤ N, 0 < n j) (hb : ∀ j < N, 0 < b j) :
    ((n 0 ^ a : ℝ) : ℂ) *
        hierarchyWeight n (fun j => Real.log (b j / n (j+1))) (fun _ => (a : ℂ)) a N =
      ((∏ j ∈ Finset.range N, (n j / b j)^a : ℝ) : ℂ) := by
  have hlogs : (∑ j ∈ Finset.range N, Real.log (n j / b j)) =
      Real.log (n 0 / n N) - ∑ j ∈ Finset.range N, Real.log (b j / n (j+1)) := by
    rw [← sum_log_ratios n N hn, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjN := Finset.mem_range.mp hj
    rw [Real.log_div (hn j (by omega)).ne' (hb j hjN).ne',
      Real.log_div (hn j (by omega)).ne' (hn (j+1) (by omega)).ne',
      Real.log_div (hb j hjN).ne' (hn (j+1) (by omega)).ne']
    ring
  have hleft : ((n 0 ^ a : ℝ) : ℂ) = Complex.exp ((a * Real.log (n 0) : ℝ) : ℂ) := by
    rw [Real.rpow_def_of_pos (hn 0 (Nat.zero_le N)), Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hterm (j : ℕ) (hj : j ∈ Finset.range N) :
      ((n j / b j)^a : ℝ) = Real.exp (a * Real.log (n j / b j)) := by
    rw [Real.rpow_def_of_pos (div_pos (hn j (by have := Finset.mem_range.mp hj; omega))
      (hb j (Finset.mem_range.mp hj)))]
    congr 1
    ring
  rw [hleft, hierarchyWeight, ← Complex.exp_add]
  rw [Finset.prod_congr rfl hterm, ← Real.exp_sum, Complex.ofReal_exp]
  congr 1
  unfold hierarchyLog
  have hscalar : a * Real.log (n 0) +
      (-a * Real.log (n N) - ∑ j ∈ Finset.range N, a * Real.log (b j / n (j+1))) =
        ∑ j ∈ Finset.range N, a * Real.log (n j / b j) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum, hlogs,
      Real.log_div (hn 0 (Nat.zero_le N)).ne' (hn N le_rfl).ne']
    ring
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hscalar
  push_cast at hc ⊢
  exact hc

end LipschitzHilbert

end

end OAI
