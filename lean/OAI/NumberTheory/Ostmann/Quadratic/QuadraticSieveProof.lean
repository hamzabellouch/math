import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGrowthBridge
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDyadicImprovement

namespace OAI

/-! # Heath-Brown's quadratic large sieve from the proved exponent descent -/

namespace Ostmann

theorem quadratic_sieve_growth_improve {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 ≤ ξ) (hξ' : ξ ≤ 2) : QuadraticSieveGrowth (quadraticImprovedExponent ξ) :=
  quadratic_growth_of_dyadic _ (quadratic_dyadic_improvement h hξ hξ')

noncomputable def quadraticSieveExponent (r : ℕ) : ℝ := 1 + 1 / ((r : ℝ) + 1)

theorem quadraticSieveExponent_bounds (r : ℕ) :
    1 ≤ quadraticSieveExponent r ∧ quadraticSieveExponent r ≤ 2 := by
  have hr : (1 : ℝ) ≤ (r : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) r; linarith
  have hdiv : 1 / ((r : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr hr
  unfold quadraticSieveExponent
  constructor <;> linarith [one_div_pos.mpr (by positivity : (0 : ℝ) < (r : ℝ) + 1)]

theorem quadraticSieveExponent_step (r : ℕ) :
    quadraticImprovedExponent (quadraticSieveExponent r) = quadraticSieveExponent (r + 1) := by
  have h₁ : (r : ℝ) + 1 ≠ 0 := by positivity
  have h₂ : (r : ℝ) + 2 ≠ 0 := by positivity
  unfold quadraticImprovedExponent quadraticSieveExponent
  push_cast
  field_simp
  ring

theorem quadratic_sieve_growth_sequence (r : ℕ) : QuadraticSieveGrowth (quadraticSieveExponent r) := by
  induction r with
  | zero =>
    convert quadratic_sieve_growth_two using 1
    norm_num [quadraticSieveExponent]
  | succ r ih =>
    rw [← quadraticSieveExponent_step]
    exact quadratic_sieve_growth_improve ih (quadraticSieveExponent_bounds r).1 (quadraticSieveExponent_bounds r).2

/-- Heath-Brown's odd-squarefree quadratic large sieve
(1995, Theorem 1), in the range used for the prime decomposition. -/
theorem publishedQuadraticLargeSieve : PublishedQuadraticLargeSieve := by
  intro ε hε
  obtain ⟨r, hr⟩ := exists_nat_gt (2 / ε)
  have hrp : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hsmall : 1 / ((r : ℝ) + 1) ≤ ε / 2 := by
    apply (div_le_iff₀ hrp).mpr
    have hh := (div_lt_iff₀ hε).mp hr
    nlinarith
  obtain ⟨C, hC, hc⟩ := quadratic_sieve_growth_sequence r (ε / 2) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro M N hM hN v
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hXp : 0 < (M : ℝ) * N := by positivity
  have hX : 1 ≤ (M : ℝ) * N := one_le_mul_of_one_le_of_one_le hMR hNR
  have hNpow : (N : ℝ) ^ (1 / ((r : ℝ) + 1)) ≤ ((M : ℝ) * N) ^ (ε / 2) := by
    apply (Real.rpow_le_rpow_of_exponent_le hNR hsmall).trans
    exact Real.rpow_le_rpow (Nat.cast_nonneg N)
      (le_mul_of_one_le_left (Nat.cast_nonneg N) hMR) (by positivity)
  have hS : (M : ℝ) + (N : ℝ) ^ quadraticSieveExponent r ≤
      (((M : ℝ) * N) ^ (ε / 2)) * ((M : ℝ) + N) := by
    rw [quadraticSieveExponent, Real.rpow_add (by positivity : (0 : ℝ) < N), Real.rpow_one]
    have hm := mul_le_mul_of_nonneg_right (Real.one_le_rpow hX (by positivity : (0 : ℝ) ≤ ε / 2))
      (Nat.cast_nonneg M)
    have hn := mul_le_mul_of_nonneg_left hNpow (Nat.cast_nonneg N)
    nlinarith only [hm, hn]
  have hp : ((M : ℝ) * N) ^ ε =
      ((M : ℝ) * N) ^ (ε / 2) * ((M : ℝ) * N) ^ (ε / 2) := by
    rw [← Real.rpow_add hXp]
    congr 1
    ring
  apply (hc M N hM hN v).trans
  calc
    _ ≤ C * ((M : ℝ) * N) ^ (ε / 2) *
        ((((M : ℝ) * N) ^ (ε / 2)) * ((M : ℝ) + N)) * quadraticSieveEnergy N v := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      exact mul_le_mul_of_nonneg_left hS (by positivity)
    _ = _ := by rw [hp]; ring

end Ostmann

end OAI
