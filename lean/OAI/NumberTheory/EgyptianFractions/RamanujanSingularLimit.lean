import OAI.NumberTheory.EgyptianFractions.RamanujanEuler
import OAI.NumberTheory.EgyptianFractions.ThreePrimeLocalSeries

namespace OAI
noncomputable section

open scoped BigOperators Topology
open Filter

namespace Problem337

/-- Inserting the neutral nonprime factors gives the canonical shifted
natural-index truncation of the prime Euler product. -/
theorem threePrimeArithmeticFactor_prod_primesLE (N u : ℕ) :
    (∏ p ∈ Nat.primesLE (N + 2), threePrimeArithmeticFactor p u) =
      threePrimeArithmeticFactor 2 u *
        ∏ n ∈ Finset.range N, threePrimeArithmeticFactor (n + 3) u := by
  classical
  rw [Nat.primesLE_eq_filter_range, Finset.prod_filter]
  have hide (p : ℕ) : (if p.Prime then threePrimeArithmeticFactor p u else 1) =
      threePrimeArithmeticFactor p u := by
    by_cases hp : p.Prime
    · simp [hp]
    · simp [hp, threePrimeArithmeticFactor_of_not_prime p u hp]
  simp_rw [hide]
  have hrange : N + 2 + 1 = 3 + N := by omega
  rw [hrange, Finset.prod_range_add]
  have hbase : (∏ p ∈ Finset.range 3, threePrimeArithmeticFactor p u) =
      threePrimeArithmeticFactor 2 u := by
    norm_num [Finset.prod_range_succ, threePrimeArithmeticFactor]
  rw [hbase]
  simp only [Nat.add_comm 3]

/-- The divisor partial sums over a primorial are actual finite cubic
Ramanujan sums and exactly equal the corresponding local-density product. -/
theorem sum_ramanujanCoefficient_primorial (N u : ℕ) :
    (∑ d ∈ (primorial (N + 2)).divisors, RamanujanEuler.coefficient d u) =
      ((threePrimeArithmeticFactor 2 u *
        ∏ n ∈ Finset.range N, threePrimeArithmeticFactor (n + 3) u : ℝ) : ℂ) := by
  rw [RamanujanEuler.sum_coefficient_divisors (squarefree_primorial _) u,
    primeFactors_primorial]
  calc
    _ = ((∏ p ∈ Nat.primesLE (N + 2), threePrimeArithmeticFactor p u : ℝ) : ℂ) := by
      rw [Complex.ofReal_prod]
      apply Finset.prod_congr rfl
      intro p hp
      rw [threePrimeArithmeticFactor_of_prime p u (Nat.prime_of_mem_primesLE hp)]
    _ = _ := by rw [threePrimeArithmeticFactor_prod_primesLE]

/-- The finite coefficient sums over divisors of expanding primorials
converge to the canonical singular series. No prime-count asymptotic is used. -/
theorem tendsto_sum_ramanujanCoefficient_primorial (u : ℕ) :
    Tendsto (fun N : ℕ =>
      ∑ d ∈ (primorial (N + 2)).divisors, RamanujanEuler.coefficient d u)
      atTop (𝓝 (threePrimeSingularSeries u : ℂ)) := by
  have hprod := (threePrimeArithmeticFactors_multipliable u).hasProd.tendsto_prod_nat
  have hreal := hprod.const_mul (threePrimeArithmeticFactor 2 u)
  rw [← threePrimeSingularSeries_eq_localProduct u] at hreal
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  simpa only [Function.comp_def, sum_ramanujanCoefficient_primorial] using hcomplex

/-- Nonsquarefree moduli contribute zero to the cubic Möbius-weighted sum. -/
lemma ramanujanCoefficient_eq_zero_of_not_squarefree (n u : ℕ)
    (hn : ¬Squarefree n) : RamanujanEuler.coefficient n u = 0 := by
  by_cases hn0 : n = 0
  · simp [RamanujanEuler.coefficient, hn0]
  · let : NeZero n := ⟨hn0⟩
    rw [RamanujanEuler.coefficient_of_ne_zero,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
    norm_num

/-- Because nonsquarefree coefficient terms vanish, the primorial-divisor
partial sums exhaust all the nonzero terms of any convergent coefficient
series. Absolute convergence itself is deliberately an explicit input. -/
theorem tendsto_sum_ramanujanCoefficient_primorial_tsum (u : ℕ)
    (hs : Summable (fun n : ℕ => RamanujanEuler.coefficient n u)) :
    Tendsto (fun N : ℕ =>
      ∑ d ∈ (primorial (N + 2)).divisors, RamanujanEuler.coefficient d u)
      atTop (𝓝 (∑' n : ℕ, RamanujanEuler.coefficient n u)) := by
  classical
  let A : ℕ → Finset ℕ := fun N => (primorial (N + 2)).divisors ∪
    (Finset.range N).filter (fun n => ¬Squarefree n)
  have hmono : Monotone A := by
    intro N M hNM d hd
    rcases Finset.mem_union.mp hd with hdiv | hnot
    · apply Finset.mem_union_left
      exact Nat.divisors_subset_of_dvd (primorial_ne_zero _)
        (primorial_dvd_primorial (by omega : N + 2 ≤ M + 2)) hdiv
    · apply Finset.mem_union_right
      obtain ⟨hdN, hdnot⟩ := Finset.mem_filter.mp hnot
      exact Finset.mem_filter.mpr ⟨Finset.range_mono hNM hdN, hdnot⟩
  have hcover : ∀ n : ℕ, ∃ N : ℕ, n ∈ A N := by
    intro n
    by_cases hn : Squarefree n
    · refine ⟨n, Finset.mem_union_left _ ?_⟩
      apply Nat.mem_divisors.mpr
      exact ⟨hn.dvd_primorial.trans (primorial_dvd_primorial (by omega)),
        primorial_ne_zero _⟩
    · exact ⟨n + 1, Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hn⟩)⟩
  have hsum (N : ℕ) : (∑ d ∈ A N, RamanujanEuler.coefficient d u) =
      ∑ d ∈ (primorial (N + 2)).divisors, RamanujanEuler.coefficient d u := by
    symm
    apply Finset.sum_subset (Finset.subset_union_left)
    intro d hd hdnot
    rcases Finset.mem_union.mp hd with hdiv | hbad
    · exact False.elim (hdnot hdiv)
    · exact ramanujanCoefficient_eq_zero_of_not_squarefree d u
        (Finset.mem_filter.mp hbad).2
  have hlimit := hs.hasSum.comp (hmono.tendsto_atTop_finset hcover)
  simpa only [Function.comp_def, hsum] using hlimit

/-- Conditional only on actual coefficient summability, the ordinary infinite
cubic Ramanujan series is exactly the canonical Euler-product singular series.
This does not provide a three-prime counting asymptotic. -/
theorem tsum_ramanujanCoefficient_eq_singularSeries (u : ℕ)
    (hs : Summable (fun n : ℕ => RamanujanEuler.coefficient n u)) :
    (∑' n : ℕ, RamanujanEuler.coefficient n u) = (threePrimeSingularSeries u : ℂ) := by
  exact tendsto_nhds_unique (tendsto_sum_ramanujanCoefficient_primorial_tsum u hs)
    (tendsto_sum_ramanujanCoefficient_primorial u)

end Problem337

end

end OAI
