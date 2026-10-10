import Mathlib.MeasureTheory.Integral.Pi
import OAI.NumberTheory.Ostmann.Construction.GiantLogMeasures

namespace OAI

/-! # Product densities for the joint Page integral -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

/-- The scalar-density factors of the ideal bulk laws multiply inside one
finite product integral. This is used with the nonnegative Page densities. -/
theorem bulk_pi_withDensity {J : Type*} [Fintype J]
    (μ : J → Measure ℝ) [∀ j, IsFiniteMeasure (μ j)]
    (ρ : J → ℝ → ℝ)
    (hi : ∀ j, Integrable (ρ j) (μ j)) (hpos : ∀ j x, 0 ≤ ρ j x) :
    Measure.pi (fun j => (μ j).withDensity (fun x => ENNReal.ofReal (ρ j x))) =
      (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ j, ρ j (x j))) := by
  let ν := fun j => (μ j).withDensity (fun x => ENNReal.ofReal (ρ j x))
  let _ : ∀ j, IsFiniteMeasure (ν j) := fun j =>
    isFiniteMeasure_withDensity ((lintegral_ofReal_ne_top_iff_integrable
      (hi j).aestronglyMeasurable (Filter.Eventually.of_forall (hpos j))).mpr (hi j))
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hp : Integrable (fun x : J → ℝ => ∏ j, ρ j (x j))
      ((Measure.pi μ).restrict (Set.univ.pi s)) := by
    rw [Measure.restrict_pi_pi]
    exact Integrable.fintype_prod (fun j => (hi j).restrict)
  rw [← ofReal_integral_eq_lintegral_ofReal hp
    (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun j _ => hpos j (x j)),
    Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  have hn (j : J) : 0 ≤ ∫ x in s j, ρ j x ∂μ j :=
    integral_nonneg (hpos j)
  rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => hn j)]
  apply Finset.prod_congr rfl
  intro j _
  rw [withDensity_apply _ (hs j),
    ← ofReal_integral_eq_lintegral_ofReal (hi j).restrict
      (Filter.Eventually.of_forall (hpos j))]

/-- Exact complex integral form of the joint density identity. -/
theorem bulk_integral_product_density {J : Type*} [Fintype J]
    (μ : J → Measure ℝ) [∀ j, IsFiniteMeasure (μ j)]
    (ρ : J → ℝ → ℝ) (hρ : ∀ j, Measurable (ρ j))
    (hi : ∀ j, Integrable (ρ j) (μ j)) (hpos : ∀ j x, 0 ≤ ρ j x)
    (f : (J → ℝ) → ℂ) :
    (∫ x, f x ∂Measure.pi (fun j => (μ j).withDensity (fun y => ENNReal.ofReal (ρ j y)))) =
      ∫ x, f x * ((∏ j, ρ j (x j) : ℝ) : ℂ) ∂Measure.pi μ := by
  rw [bulk_pi_withDensity μ ρ hi hpos]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (Measurable.ennreal_ofReal (by fun_prop)).aemeasurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun j _ => hpos j (x j)),
      Complex.real_smul, mul_comm]

end Ostmann

end OAI
