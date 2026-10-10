import OAI.NumberTheory.EgyptianFractions.VaughanDyadicDecomposition
import OAI.NumberTheory.EgyptianFractions.VaughanHyperbolicNearRational

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction
open Finset

namespace Problem337.Vaughan

lemma typeIIBlock_eq_bilinear (θ : ℝ) (N U V j : ℕ) :
    typeIIBlock N U V j (fun k => VaughanBilinear.phase (θ * k)) =
      ∑ m ∈ Icc (max (U + 1) (2 ^ j)) (min N (2 ^ (j + 1) - 1)),
        (typeIICoefficient U m : ℂ) *
          ∑ n ∈ Ioc V (N / 2 ^ j), (Λ n : ℂ) *
            HyperbolaCorrelation.column θ N n m := by
  unfold typeIIBlock VaughanDyadic.block
  rw [VaughanDyadic.shell_eq_Icc]
  apply sum_congr rfl
  intro m hm
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  unfold HyperbolaCorrelation.column
  by_cases h : m * n ≤ N
  · simp only [ite_eq_left h, HyperbolaCorrelation.phase_eq_vaughan]
    rw [mul_assoc]
    congr 2
    congr 1
    push_cast
    ring
  · simp [h]

lemma dyadic_row_length_le (N U j : ℕ) :
    min N (2 ^ (j + 1) - 1) + 1 - max (U + 1) (2 ^ j) ≤ 2 ^ j := by
  have htop : min N (2 ^ (j + 1) - 1) ≤ 2 ^ (j + 1) - 1 := min_le_right _ _
  have hlow : 2 ^ j ≤ max (U + 1) (2 ^ j) := le_max_right _ _
  have hp : 0 < 2 ^ j := by positivity
  rw [pow_succ] at htop
  omega

/-- The elementary bounded-weight column energy, used only as a normalization
inside the actual Type II block estimate. -/
lemma mangoldt_column_energy_le (V T : ℕ) :
    (∑ n ∈ Ioc V T, ‖(Λ n : ℂ)‖ ^ 2) ≤ (T : ℝ) * (Real.log T) ^ 2 := by
  calc
    _ ≤ ∑ n ∈ Ioc V T, (Real.log T) ^ 2 := by
      apply sum_le_sum
      intro n hn
      have h := mem_Ioc.mp hn
      have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le V) h.1
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast h.2))
    _ = ((T - V : ℕ) : ℝ) * (Real.log T) ^ 2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le T V) (sq_nonneg _)

/-- A genuine rational-approximation estimate for one actual Vaughan block.
All coefficient energies and correlations have been evaluated explicitly. -/
theorem typeIIBlock_sq_le_raw
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N U V j : ℕ) :
    ‖typeIIBlock N U V j (fun k => VaughanBilinear.phase (θ * k))‖ ^ 2 ≤
      ((2 ^ (j + 1) : ℕ) * (1 + Real.log (2 ^ (j + 1) : ℕ)) ^ 3) *
        ((2 * ((N / 2 ^ j : ℕ) : ℝ) / q + 1) *
          (2 * ((2 ^ j : ℕ) : ℝ) + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))))) *
            (((N / 2 ^ j : ℕ) : ℝ) * (Real.log (N / 2 ^ j : ℕ)) ^ 2) := by
  have hlog : 0 ≤ 1 + Real.log (2 * (q : ℝ)) := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 * q by linarith)
    linarith
  have h := VaughanBilinear.near_rational_hyperbolic_bilinear_sq_le θ a q hq hcop happrox
    N (max (U + 1) (2 ^ j)) (min N (2 ^ (j + 1) - 1)) (V + 1) (N / 2 ^ j)
    (Ioc V (N / 2 ^ j)) (by
      intro n hn
      have hn' := mem_Ioc.mp hn
      exact mem_Ico.mpr ⟨by omega, by omega⟩)
    (fun n hn => lt_of_le_of_lt (Nat.zero_le V) (mem_Ioc.mp hn).1)
    (fun m => (typeIICoefficient U m : ℂ)) (fun n => (Λ n : ℂ))
  rw [← typeIIBlock_eq_bilinear, ← VaughanDyadic.shell_eq_Icc] at h
  refine h.trans ?_
  have hA := typeII_shell_energy_le N U j
  have hB := mangoldt_column_energy_le V (N / 2 ^ j)
  have hlength : ((min N (2 ^ (j + 1) - 1) + 1 - max (U + 1) (2 ^ j) : ℕ) : ℝ) ≤
      ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast dyadic_row_length_le N U j
  gcongr

end Problem337.Vaughan

end

end OAI
