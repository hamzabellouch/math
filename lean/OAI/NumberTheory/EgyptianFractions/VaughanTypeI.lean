import OAI.NumberTheory.EgyptianFractions.VaughanWeighted
import OAI.NumberTheory.EgyptianFractions.ThreePrimePartialSummation

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Problem337.Vaughan

/-- Indexing positive initial intervals by a zero-based range. -/
lemma sum_Ioc_zero_eq_sum_range_succ {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (N : ℕ) :
    (∑ j ∈ Finset.Ioc 0 N, f j) = ∑ j ∈ Finset.range N, f (j + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le N), Finset.sum_range_succ, ih]

/-- Adding a logarithmic weight costs at most twice the endpoint logarithm.
The prefix bound remains explicit; no cancellation estimate is assumed silently. -/
theorem log_weighted_sum_norm_le (w : ℕ → ℂ) (N : ℕ) (B : ℝ)
    (hprefix : ∀ k ≤ N, ‖∑ j ∈ Finset.Ioc 0 k, w j‖ ≤ B) :
    ‖∑ j ∈ Finset.Ioc 0 N, (Real.log j : ℂ) * w j‖ ≤
      2 * B * Real.log N := by
  cases N with
  | zero => simp
  | succ n =>
    have hlog (j : ℕ) : 0 ≤ Real.log (j + 1 : ℕ) :=
      Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j))
    have hmono (j : ℕ) : Real.log (j + 1 : ℕ) ≤ Real.log (j + 1 + 1 : ℕ) := by
      apply Real.log_le_log
      · positivity
      · exact_mod_cast Nat.le_succ (j + 1)
    have hvar : (∑ j ∈ Finset.range n,
        ‖(Real.log (j + 1 + 1 : ℕ) : ℂ) - (Real.log (j + 1 : ℕ) : ℂ)‖) =
        Real.log (n + 1 : ℕ) := by
      calc
        _ = ∑ j ∈ Finset.range n,
            (Real.log (j + 1 + 1 : ℕ) - Real.log (j + 1 : ℕ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.mpr (hmono j))]
        _ = _ := by
          simpa using Finset.sum_range_sub (fun j => Real.log (j + 1 : ℕ)) n
    have h := ThreePrimeAnalysis.weighted_sum_norm_le_partial_sum_bound
      (fun j => w (j + 1)) (fun j => (Real.log (j + 1 : ℕ) : ℂ)) n B (by
        intro k hk
        simpa only [sum_Ioc_zero_eq_sum_range_succ] using hprefix k hk)
    rw [hvar, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hlog n)] at h
    rw [sum_Ioc_zero_eq_sum_range_succ]
    convert h using 1
    ring

/-- Type I logarithmic bilinear estimate for coefficients bounded by one. -/
theorem norm_log_bilinear_sum_le (w : ℕ → ℂ) (N A : ℕ) (c B : ℕ → ℝ)
    (hA : A ≤ N)
    (hc : ∀ a ∈ Finset.Ioc 0 A, |c a| ≤ 1)
    (hprefix : ∀ a ∈ Finset.Ioc 0 A, ∀ k ≤ N / a,
      ‖∑ b ∈ Finset.Ioc 0 k, w (a * b)‖ ≤ B a) :
    ‖∑ a ∈ Finset.Ioc 0 A, (c a : ℂ) *
        ∑ b ∈ Finset.Ioc 0 (N / a), (Real.log b : ℂ) * w (a * b)‖ ≤
      2 * Real.log N * ∑ a ∈ Finset.Ioc 0 A, B a := by
  calc
    _ ≤ ∑ a ∈ Finset.Ioc 0 A,
        ‖(c a : ℂ) * ∑ b ∈ Finset.Ioc 0 (N / a),
          (Real.log b : ℂ) * w (a * b)‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ Finset.Ioc 0 A, 2 * Real.log N * B a := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨ha0, haA⟩ := Finset.mem_Ioc.mp ha
      have haN := haA.trans hA
      have hq : 1 ≤ N / a := (Nat.le_div_iff_mul_le ha0).mpr (by simpa using haN)
      have hB : 0 ≤ B a := by simpa using hprefix a ha 0 (Nat.zero_le _)
      have hlog : Real.log (N / a : ℕ) ≤ Real.log N := by
        apply Real.log_le_log
        · exact_mod_cast (Nat.zero_lt_of_lt hq)
        · exact_mod_cast Nat.div_le_self N a
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ ≤ 1 * ‖∑ b ∈ Finset.Ioc 0 (N / a),
            (Real.log b : ℂ) * w (a * b)‖ :=
          mul_le_mul_of_nonneg_right (hc a ha) (norm_nonneg _)
        _ ≤ 2 * B a * Real.log (N / a : ℕ) := by
          simpa using log_weighted_sum_norm_le (fun b => w (a * b)) (N / a) (B a)
            (hprefix a ha)
        _ ≤ 2 * Real.log N * B a := by
          nlinarith [mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * B a by positivity)]
    _ = _ := by rw [Finset.mul_sum]

/-- Type I bilinear estimate for coefficients with the logarithmic majorant. -/
theorem norm_bilinear_sum_le_log (w : ℕ → ℂ) (N A : ℕ) (c B : ℕ → ℝ)
    (hA : A ≤ N)
    (hc : ∀ a ∈ Finset.Ioc 0 A, |c a| ≤ Real.log a)
    (hinner : ∀ a ∈ Finset.Ioc 0 A,
      ‖∑ b ∈ Finset.Ioc 0 (N / a), w (a * b)‖ ≤ B a) :
    ‖∑ a ∈ Finset.Ioc 0 A, (c a : ℂ) *
        ∑ b ∈ Finset.Ioc 0 (N / a), w (a * b)‖ ≤
      Real.log N * ∑ a ∈ Finset.Ioc 0 A, B a := by
  calc
    _ ≤ ∑ a ∈ Finset.Ioc 0 A,
        ‖(c a : ℂ) * ∑ b ∈ Finset.Ioc 0 (N / a), w (a * b)‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ Finset.Ioc 0 A, Real.log N * B a := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨ha0, haA⟩ := Finset.mem_Ioc.mp ha
      have hB : 0 ≤ B a := (norm_nonneg _).trans (hinner a ha)
      have hlog : Real.log a ≤ Real.log N := Real.log_le_log
        (by exact_mod_cast ha0) (by exact_mod_cast haA.trans hA)
      have hlogN : 0 ≤ Real.log N := (abs_nonneg _).trans ((hc a ha).trans hlog)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul ((hc a ha).trans hlog) (hinner a ha) (norm_nonneg _) hlogN
    _ = _ := by rw [Finset.mul_sum]

/-- The first Vaughan Type I term in its finite bilinear form. -/
theorem first_typeI_sum_bound (w : ℕ → ℂ) (N U : ℕ) (B : ℕ → ℝ)
    (hprefix : ∀ a ∈ Finset.Ioc 0 (min U N), ∀ k ≤ N / a,
      ‖∑ b ∈ Finset.Ioc 0 k, w (a * b)‖ ≤ B a) :
    ‖∑ a ∈ Finset.Ioc 0 (min U N), ((μ a : ℝ) : ℂ) *
        ∑ b ∈ Finset.Ioc 0 (N / a), (Real.log b : ℂ) * w (a * b)‖ ≤
      2 * Real.log N * ∑ a ∈ Finset.Ioc 0 (min U N), B a := by
  apply norm_log_bilinear_sum_le w N (min U N) (fun a => (μ a : ℝ)) B
    (min_le_right _ _) _ hprefix
  intro a ha
  exact abs_real_moebius_le_one a

/-- The second Vaughan Type I term in its finite bilinear form. -/
theorem second_typeI_sum_bound (w : ℕ → ℂ) (N U V : ℕ) (B : ℕ → ℝ)
    (hinner : ∀ a ∈ Finset.Ioc 0 (min (U * V) N),
      ‖∑ b ∈ Finset.Ioc 0 (N / a), w (a * b)‖ ≤ B a) :
    ‖∑ a ∈ Finset.Ioc 0 (min (U * V) N), (typeICoefficient U V a : ℂ) *
        ∑ b ∈ Finset.Ioc 0 (N / a), w (a * b)‖ ≤
      Real.log N * ∑ a ∈ Finset.Ioc 0 (min (U * V) N), B a := by
  exact norm_bilinear_sum_le_log w N (min (U * V) N) (typeICoefficient U V) B
    (min_le_right _ _) (fun a _ => abs_typeICoefficient_le_log U V a) hinner

/-- First Type I estimate directly for the actual Vaughan convolution. -/
theorem first_typeI_bound (w : ℕ → ℂ) (N U : ℕ) (B : ℕ → ℝ)
    (hprefix : ∀ a ∈ Finset.Ioc 0 (min U N), ∀ k ≤ N / a,
      ‖∑ b ∈ Finset.Ioc 0 k, w (a * b)‖ ≤ B a) :
    ‖weightedSum (Finset.Ioc 0 N) w
        (shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)‖ ≤
      2 * Real.log N * ∑ a ∈ Finset.Ioc 0 (min U N), B a := by
  rw [first_typeI_eq_sum]
  exact first_typeI_sum_bound w N U B hprefix

/-- Second Type I estimate directly for the actual Vaughan convolution. -/
theorem second_typeI_bound (w : ℕ → ℂ) (N U V : ℕ) (B : ℕ → ℝ)
    (hinner : ∀ a ∈ Finset.Ioc 0 (min (U * V) N),
      ‖∑ b ∈ Finset.Ioc 0 (N / a), w (a * b)‖ ≤ B a) :
    ‖weightedSum (Finset.Ioc 0 N) w (typeICoefficient U V * ζ)‖ ≤
      Real.log N * ∑ a ∈ Finset.Ioc 0 (min (U * V) N), B a := by
  rw [second_typeI_eq_sum]
  exact second_typeI_sum_bound w N U V B hinner

end Problem337.Vaughan

end

end OAI
