import OAI.NumberTheory.Ostmann.ZeroDensity.GiantHaarDensity

namespace OAI

/-! # The ideal giant main terms as a common real integral of Haar averages -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators Classical

theorem primeGiantMeasure_pair_haar_integral (P : PublishedProgressionInput) (Q q : ℕ) [NeZero q]
    (u v r s : ℝ) (hu : 1 ≤ u) (hr : 1 ≤ r)
    (H : ℝ → ℝ → ℂ) (hH : Measurable (Function.uncurry H)) (K : ℝ)
    (hK : ∀ x y, ‖H x y‖ ≤ K) (c : ℕ → ℕ → ℂ) :
    (∑ b ∈ reducedResidues q, ∑ a ∈ reducedResidues q,
      ∫ x, ∫ y, c a b * H x y ∂primeGiantMeasure P Q q b r s ∂primeGiantMeasure P Q q a u v) =
      ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
        H x y * correctedPrimePairAverage P Q q c x y / ((x : ℂ) * (y : ℂ)) := by
  rw [Finset.sum_comm, primeGiantMeasure_residue_integral P Q q (NeZero.pos q)
    (reducedResidues q) (reducedResidues q) u v r s hu hr H hH K hK c]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  apply setIntegral_congr_fun measurableSet_Ioc
  intro y hy
  simp only [restrictedPrimeGiantDensity, Set.indicator_of_mem hx, Set.indicator_of_mem hy]
  rw [prime_pair_density_haar]
  ring

theorem mixedGiantMeasure_pair_haar_integral (P : PublishedProgressionInput) (Q q : ℕ) [NeZero q]
    (u v r s J : ℝ) (hr : 1 ≤ r)
    (H : ℝ → ℝ → ℂ) (hH : Measurable (Function.uncurry H)) (K : ℝ)
    (hK : ∀ x y, ‖H x y‖ ≤ K) (c : ℕ → ℕ → ℂ) :
    (∑ b ∈ reducedResidues q, ∑ a ∈ Finset.range q,
      ∫ x, ∫ y, c a b * H x y ∂primeGiantMeasure P Q q b r s ∂integerGiantMeasure q J u v) =
      ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
        H x y * (Real.exp (x - J) : ℂ) * correctedMixedPairAverage P Q q c y / (y : ℂ) := by
  rw [Finset.sum_comm, mixedGiantMeasure_residue_integral P Q q (NeZero.pos q)
    (Finset.range q) (reducedResidues q) u v r s J hr H hH K hK c]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  apply setIntegral_congr_fun measurableSet_Ioc
  intro y hy
  simp only [restrictedIntegerGiantDensity, restrictedPrimeGiantDensity,
    Set.indicator_of_mem hx, Set.indicator_of_mem hy]
  rw [mixed_pair_density_haar]
  ring

end Ostmann

end OAI
