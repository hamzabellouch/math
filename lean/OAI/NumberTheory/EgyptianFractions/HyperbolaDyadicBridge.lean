import OAI.NumberTheory.EgyptianFractions.VaughanDyadic
import OAI.NumberTheory.EgyptianFractions.HyperbolaTypeII

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.VaughanDyadic

/-- Empty high shells contribute nothing to the long--long hyperbola. -/
theorem block_eq_zero_of_large_base {E : Type*} [AddCommMonoid E]
    (N U V j : ℕ) (F : ℕ → ℕ → E) (hN : N < 2 ^ j * (V + 1)) :
    block N U V j F = 0 := by
  unfold block
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro n hn
  have hm2 := (mem_shell.mp hm).2.2.1
  have hnV : V + 1 ≤ n := (Finset.mem_Ioc.mp hn).1
  have hmn : N < m * n := hN.trans_le (Nat.mul_le_mul hm2 hnV)
  simp [not_le.mpr hmn]

/-- Every nonzero block has row scale at most the hyperbolic long-column cap. -/
theorem base_le_div_of_block_ne_zero {E : Type*} [AddCommMonoid E]
    (N U V j : ℕ) (F : ℕ → ℕ → E) (hblock : block N U V j F ≠ 0) :
    2 ^ j ≤ N / (V + 1) := by
  apply (Nat.le_div_iff_mul_le (Nat.succ_pos V)).mpr
  by_contra h
  exact hblock (block_eq_zero_of_large_base N U V j F (Nat.lt_of_not_ge h))

/-- The clipped contiguous shell has length at most its lower power-of-two scale. -/
theorem shell_length_le (N U j : ℕ) :
    min N (2 ^ (j + 1) - 1) + 1 - max (U + 1) (2 ^ j) ≤ 2 ^ j := by
  have hp : 0 < 2 ^ j := by positivity
  rw [pow_succ]
  omega

theorem shell_card_le (N U j : ℕ) : (shell U N j).card ≤ 2 ^ j := by
  rw [shell_eq_Icc, Nat.card_Icc]
  exact shell_length_le N U j

/-- The exact dyadic phase block is the column expression used by the
hyperbolic correlation theorem, with no rectangular relaxation. -/
theorem phase_block_eq_columns (α : ℝ) (N U V j : ℕ) (a b : ℕ → ℂ) :
    block N U V j (fun m n =>
      a m * b n * HyperbolaCorrelation.phase (α * (m : ℝ) * (n : ℝ))) =
    ∑ m ∈ Finset.Icc (max (U + 1) (2 ^ j)) (min N (2 ^ (j + 1) - 1)),
      a m * ∑ n ∈ Finset.Ioc V (N / 2 ^ j),
        b n * HyperbolaCorrelation.column α N n m := by
  unfold block
  rw [shell_eq_Icc]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  unfold HyperbolaCorrelation.column
  split_ifs <;> simp [mul_assoc]

/-- A geometric row estimate at scale `2^j` controls the actual dyadic block,
retaining both coefficient energies and the moving hyperbolic endpoint. -/
theorem norm_phase_block_sq_le_energy
    (α : ℝ) (N U V j : ℕ) (a b : ℕ → ℂ) (C : ℝ)
    (hrow : ∀ n ∈ Finset.Ioc V (N / 2 ^ j),
      (∑ k ∈ Finset.Ioc V (N / 2 ^ j),
        VaughanBilinear.geometricBound (2 ^ j) (α * ((n : ℝ) - (k : ℝ)))) ≤ C) :
    ‖block N U V j (fun m n =>
      a m * b n * HyperbolaCorrelation.phase (α * (m : ℝ) * (n : ℝ)))‖ ^ 2 ≤
      (∑ m ∈ shell U N j, ‖a m‖ ^ 2) * C *
        (∑ n ∈ Finset.Ioc V (N / 2 ^ j), ‖b n‖ ^ 2) := by
  rw [phase_block_eq_columns, shell_eq_Icc]
  apply HyperbolaCorrelation.norm_hyperbolic_bilinear_sq_le_energy
    α N (max (U + 1) (2 ^ j)) (min N (2 ^ (j + 1) - 1))
    (Finset.Ioc V (N / 2 ^ j)) a b
    (fun n hn => lt_of_le_of_lt (Nat.zero_le V) (Finset.mem_Ioc.mp hn).1) C
  intro n hn
  refine (Finset.sum_le_sum fun k hk => ?_).trans (hrow n hn)
  exact HyperbolaCorrelation.geometricBound_mono (shell_length_le N U j) _

end Problem337.VaughanDyadic

end

end OAI
