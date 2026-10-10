import OAI.Analysis.CircleDomains.Sobolev.MetricIntegral

namespace OAI

/-!
# Wedge products control the optimized metric energy

The two-dimensional Cauchy–Binet identity is proved directly for finite
lists of coordinate differentials. No rank or determinant identity is
assumed. The resulting bound is the pointwise algebra behind the
finite-transfer energy estimate.
-/

open Finset

namespace CircleDomainRigidity.FiniteTransfer

/-- Cauchy–Binet for the Gram matrix of a finite family of two-dimensional
covectors, with each unordered pair counted once. -/
theorem gramDet_eq_wedgeSquares (x y : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range n, x i ^ 2) * (∑ i ∈ range n, y i ^ 2) -
      (∑ i ∈ range n, x i * y i) ^ 2 =
    ∑ j ∈ range n, ∑ i ∈ range j, (x i * y j - x j * y i) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsum : (∑ i ∈ range n, (x i * y n - x n * y i) ^ 2) =
        y n ^ 2 * (∑ i ∈ range n, x i ^ 2) +
        x n ^ 2 * (∑ i ∈ range n, y i ^ 2) -
        (2 * x n * y n) * (∑ i ∈ range n, x i * y i) := by
      calc
        _ = ∑ i ∈ range n, (y n ^ 2 * x i ^ 2 + x n ^ 2 * y i ^ 2 -
            (2 * x n * y n) * (x i * y i)) := by
          apply sum_congr rfl
          intro i _
          ring
        _ = _ := by
          rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
    simp only [sum_range_succ]
    rw [← ih, hsum]
    ring

/-- The square root of the Gram determinant is bounded by the sum of the
absolute wedge products. This uses the full finite list without a
pairwise-independence assumption. -/
theorem sqrt_gramDet_le_wedges (x y : ℕ → ℝ) (n : ℕ) :
    Real.sqrt ((∑ i ∈ range n, x i ^ 2) * (∑ i ∈ range n, y i ^ 2) -
      (∑ i ∈ range n, x i * y i) ^ 2) ≤
    ∑ j ∈ range n, ∑ i ∈ range j, |x i * y j - x j * y i| := by
  rw [gramDet_eq_wedgeSquares]
  have hinner (j : ℕ) :
      (∑ i ∈ range j, (x i * y j - x j * y i) ^ 2) ≤
        (∑ i ∈ range j, |x i * y j - x j * y i|) ^ 2 := by
    simpa only [sq_abs] using sum_sq_le_sq_sum_of_nonneg
      (s := range j) (f := fun i => |x i * y j - x j * y i|)
      (fun i _ => abs_nonneg _)
  have hnonneg (j : ℕ) : 0 ≤ ∑ i ∈ range j, |x i * y j - x j * y i| :=
    sum_nonneg fun _ _ => abs_nonneg _
  have hsum := sum_le_sum (s := range n) (fun j _ => hinner j)
  have houter := sum_sq_le_sq_sum_of_nonneg (s := range n)
    (f := fun j => ∑ i ∈ range j, |x i * y j - x j * y i|) (fun j _ => hnonneg j)
  exact Real.sqrt_le_iff.mpr ⟨sum_nonneg (fun j _ => hnonneg j), hsum.trans houter⟩

end CircleDomainRigidity.FiniteTransfer

end OAI
