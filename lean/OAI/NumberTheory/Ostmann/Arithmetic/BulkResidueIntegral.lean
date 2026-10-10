import OAI.NumberTheory.Ostmann.Arithmetic.BulkPageProductIntegral
import OAI.NumberTheory.Ostmann.Arithmetic.BulkIntegrands

namespace OAI

/-! # Keeping residue sums inside the real bulk integral -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

/-- The full bounded sharp kernel is integrable against the product density. -/
theorem BulkIntegrand.page_density_integrable {J : Type*} [Fintype J]
    (f : BulkIntegrand J) (P : PublishedProgressionInput) (Q : ℕ)
    (q a : J → ℕ) (u v : J → ℝ) (hu : ∀ j, 0 < u j) :
    Integrable (fun x => f x * ∏ j, (selectedPrimeLogDensity P Q (q j) (a j) (x j) : ℂ))
      (Measure.pi (fun j => volume.restrict (Set.Ioc (u j) (v j)))) := by
  have hp : Integrable (fun x : J → ℝ => ∏ j, (selectedPrimeLogDensity P Q (q j) (a j) (x j) : ℂ))
      (Measure.pi (fun j => volume.restrict (Set.Ioc (u j) (v j)))) := by
    exact Integrable.fintype_prod (f := fun j x =>
      (selectedPrimeLogDensity P Q (q j) (a j) x : ℂ))
      (fun j => (selectedPrimeLogDensity_integrable P Q (q j) (a j) (u j) (v j) (hu j)).ofReal)
  obtain ⟨C, _, hC⟩ := f.bounded
  exact hp.bdd_mul f.measurable.aestronglyMeasurable (Filter.Eventually.of_forall hC)

/-- Residue classes are summed inside the real integral. In particular there
is no number-of-boxes factor on the main term. -/
theorem bulk_page_residue_integral {J Z : Type*} [Fintype J] [Fintype Z]
    (P : PublishedProgressionInput) (Q : ℕ) (q : J → ℕ) (a : Z → J → ℕ)
    (u v : J → ℝ) (hu : ∀ j, 0 < u j) (f : Z → BulkIntegrand J) :
    (∑ z, ∫ x, f z x ∂Measure.pi (fun j => primeGiantMeasure P Q (q j) (a z j) (u j) (v j))) =
      ∫ x, ∑ z, f z x * ∏ j, (selectedPrimeLogDensity P Q (q j) (a z j) (x j) : ℂ)
        ∂Measure.pi (fun j => volume.restrict (Set.Ioc (u j) (v j))) := by
  simp_rw [bulk_page_product_integral P Q q _ u v hu]
  exact (integral_finsetSum _ (fun z _ => (f z).page_density_integrable P Q q (a z) u v hu)).symm

end Ostmann

end OAI
