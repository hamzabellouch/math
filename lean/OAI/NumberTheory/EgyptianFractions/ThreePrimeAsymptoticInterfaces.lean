import OAI.NumberTheory.EgyptianFractions.ThreePrimeAnalyticReduction
import OAI.NumberTheory.EgyptianFractions.ThreePrimeMangoldtAsymptotics

namespace OAI
noncomputable section
open Filter Asymptotics

namespace Problem337

/-- The explicit epsilon formulation and the standard little-oh formulation
of the ternary asymptotic agree on the filter of odd integers tending to infinity. -/
theorem ternaryMangoldtAsymptotic_iff_isLittleO :
    TernaryMangoldtAsymptotic ↔
      ((fun u : ℕ => mangoldtTripleSum u -
        (1 / 2 : ℝ) * threePrimeSingularSeries u * (u : ℝ) ^ 2) =o[
          atTop ⊓ principal {u : ℕ | Odd u}]
        (fun u : ℕ => (u : ℝ) ^ 2)) := by
  constructor
  · intro h
    apply IsLittleO.of_bound
    intro ε hε
    rw [eventually_inf_principal]
    filter_upwards [h ε hε] with u hu
    intro hodd
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (u : ℝ))] using hu hodd
  · intro h ε hε
    have hh := h.bound hε
    rw [eventually_inf_principal] at hh
    filter_upwards [hh] with u hu
    intro hodd
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (u : ℝ))] using hu hodd

/-- Prime-power removal preserves the actual varying singular-series main
term, not just the existence of some positive lower-bound constant. -/
theorem ternaryMangoldtAsymptotic_iff_prime_isLittleO :
    TernaryMangoldtAsymptotic ↔
      ((fun u : ℕ => primeTripleLogSum u -
        (1 / 2 : ℝ) * threePrimeSingularSeries u * (u : ℝ) ^ 2) =o[
          atTop ⊓ principal {u : ℕ | Odd u}]
        (fun u : ℕ => (u : ℝ) ^ 2)) := by
  rw [ternaryMangoldtAsymptotic_iff_isLittleO]
  exact mangoldt_prime_quadratic_asymptotic_iff_filter _ inf_le_left
    (fun u => (1 / 2 : ℝ) * threePrimeSingularSeries u)

/-- The canonical prime-weighted Fourier interface may be used directly in
place of the Mangoldt convolution. The little-oh estimate remains a hypothesis. -/
theorem quantitativeThreePrimeLowerBound_of_weighted_singular_isLittleO
    (h : (fun u : ℕ => weightedSupplyPrimeTriples u -
      (1 / 2 : ℝ) * threePrimeSingularSeries u * (u : ℝ) ^ 2) =o[
        atTop ⊓ principal {u : ℕ | Odd u}]
      (fun u : ℕ => (u : ℝ) ^ 2)) : QuantitativeThreePrimeLowerBound := by
  apply quantitativeThreePrimeLowerBound_of_ternary_mangoldt_asymptotic
  apply ternaryMangoldtAsymptotic_iff_prime_isLittleO.mpr
  simpa only [primeTripleLogSum_eq_weightedSupplyPrimeTriples] using h

end Problem337

end

end OAI
