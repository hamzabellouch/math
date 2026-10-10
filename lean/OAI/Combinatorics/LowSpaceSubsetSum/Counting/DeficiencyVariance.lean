import OAI.Combinatorics.LowSpaceSubsetSum.Counting.Deficiency
import OAI.Combinatorics.BalancedRyser.Probability.FiniteUniformVariance

namespace OAI

/-!
# Deficiency under sampling without replacement

The variance estimate in the paper's deficiency lemma is a specialization
of the finite completion-coupling theorem
`Balanced.WithoutReplacement.finiteVariance_powersetCard_le`.
Its probability space is exactly the uniform law on all size-`v` subsets
of the supplied domain `U`, including the cases `v = 0` and `v = |U|`.
-/

namespace LowSpaceSubsetSum

open scoped BigOperators
open Balanced.WithoutReplacement

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Mean deficiency of a uniform size-`v` subset of `U`. -/
noncomputable def meanDeficiency (a : ι → ℤ) (U : Finset ι) (v : ℕ) : ℝ :=
  𝔼 V ∈ U.powersetCard v, deficiency a V

/-- Variance for uniform sampling of exactly `v` indices, without replacement. -/
noncomputable def deficiencyVariance (a : ι → ℤ) (U : Finset ι) (v : ℕ) : ℝ :=
  finiteVariance (U.powersetCard v) (deficiency a)

theorem deficiency_exchange_bound (a : ι → ℤ) (S : Finset ι) {i j : ι}
    (hi : i ∈ S) (hj : j ∉ S) :
    |deficiency a S - deficiency a (insert j (S.erase i))| ≤ 1 := by
  have hj' : j ∉ S.erase i := fun h => hj (Finset.mem_erase.mp h).2
  simpa only [Finset.insert_erase hi] using
    (deficiency_replacement_lipschitz a (Finset.notMem_erase i S) hj')

/-- The paper's exact variance bound `Var(d(V)) ≤ v`. -/
theorem deficiencyVariance_le (a : ι → ℤ) (U : Finset ι) (v : ℕ)
    (hv : v ≤ U.card) : deficiencyVariance a U v ≤ v := by
  have h := finiteVariance_powersetCard_le U v (deficiency a)
    (c := 1) zero_le_one hv (by
      intro S _ _ i hi j _ hj
      exact deficiency_exchange_bound a S hi hj)
  simpa only [deficiencyVariance, one_pow, mul_one] using h

theorem deficiency_centered_secondMoment_le (a : ι → ℤ) (U : Finset ι) (v : ℕ)
    (hv : v ≤ U.card) :
    (𝔼 V ∈ U.powersetCard v, (deficiency a V - meanDeficiency a U v) ^ 2) ≤ v :=
  deficiencyVariance_le a U v hv

/-- A direct finite Chebyshev bound for deviations from the mean deficiency.
The left side is the exact probability under uniform size-`v` sampling. -/
theorem deficiency_tail_fraction_le (a : ι → ℤ) (U : Finset ι) (v : ℕ)
    (hv : v ≤ U.card) {t : ℝ} (ht : 0 < t) :
    (((U.powersetCard v).filter
      (fun V => t ≤ |deficiency a V - meanDeficiency a U v|)).card : ℝ) /
        (U.powersetCard v).card ≤ (v : ℝ) / t ^ 2 := by
  classical
  let D := U.powersetCard v
  let B := D.filter fun V => t ≤ |deficiency a V - meanDeficiency a U v|
  have hD : (0 : ℝ) < D.card := by
    exact_mod_cast (Finset.powersetCard_nonempty.mpr hv).card_pos
  have hpoint : ∀ V ∈ D,
      (if t ≤ |deficiency a V - meanDeficiency a U v| then t ^ 2 else 0) ≤
        (deficiency a V - meanDeficiency a U v) ^ 2 := by
    intro V _
    split_ifs with h
    · have hsq := (sq_le_sq₀ ht.le (abs_nonneg _)).mpr h
      simpa only [sq_abs] using hsq
    · exact sq_nonneg _
  have htail : (B.card : ℝ) * t ^ 2 ≤
      ∑ V ∈ D, (deficiency a V - meanDeficiency a U v) ^ 2 := by
    calc
      _ = ∑ V ∈ D,
          if t ≤ |deficiency a V - meanDeficiency a U v| then t ^ 2 else 0 := by
        rw [← Finset.sum_filter]
        simp [B]
      _ ≤ _ := Finset.sum_le_sum hpoint
  have hvar : (∑ V ∈ D, (deficiency a V - meanDeficiency a U v) ^ 2) ≤
      (v : ℝ) * D.card := by
    have h := deficiency_centered_secondMoment_le a U v hv
    rw [Finset.expect_eq_sum_div_card] at h
    exact (div_le_iff₀ hD).mp h
  change (B.card : ℝ) / D.card ≤ (v : ℝ) / t ^ 2
  exact (div_le_div_iff₀ hD (sq_pos_of_pos ht)).mpr (htail.trans hvar)

/-- Measure-theoretic form for the actual uniform fixed-cardinality law. -/
theorem deficiency_uniform_variance_le
    [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]
    (a : ι → ℤ) (U : Finset ι) (v : ℕ) (hv : v ≤ U.card) :
    ProbabilityTheory.variance (deficiency a)
      (PMF.uniformOfFinset (U.powersetCard v)
        (Finset.powersetCard_nonempty.mpr hv)).toMeasure ≤ v := by
  rw [variance_uniformOfFinset]
  exact deficiencyVariance_le a U v hv

end LowSpaceSubsetSum

end OAI
