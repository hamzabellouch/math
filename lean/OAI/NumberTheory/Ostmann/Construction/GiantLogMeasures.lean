import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import OAI.NumberTheory.Ostmann.Arithmetic.MovingKernelRates

namespace OAI

/-! # The actual ideal giant measures, including the retained Page density -/

namespace Ostmann
open MeasureTheory
open scoped ENNReal

noncomputable def intervalDensityMeasure (u v : ℝ) (ρ : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioc u v)).withDensity (fun x => ENNReal.ofReal (ρ x))

theorem finite_intervalDensityMeasure (u v : ℝ) (ρ : ℝ → ℝ)
    (hρ : IntegrableOn ρ (Set.Ioc u v)) (hpos : ∀ x ∈ Set.Ioc u v, 0 ≤ ρ x) :
    IsFiniteMeasure (intervalDensityMeasure u v ρ) := by
  apply isFiniteMeasure_withDensity
  exact (lintegral_ofReal_ne_top_iff_integrable hρ.aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioc hpos)).mpr hρ

theorem intervalDensityMeasure_integral (u v : ℝ) (ρ : ℝ → ℝ)
    (hρ : AEMeasurable ρ (volume.restrict (Set.Ioc u v)))
    (hpos : ∀ x ∈ Set.Ioc u v, 0 ≤ ρ x) (f : ℝ → ℂ) :
    (∫ x, f x ∂intervalDensityMeasure u v ρ) =
      ∫ x in Set.Ioc u v, f x * (ρ x : ℂ) := by
  unfold intervalDensityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀ hρ.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [ENNReal.toReal_ofReal (hpos x hx), Complex.real_smul, mul_comm]

theorem intervalDensityMeasure_mass (u v : ℝ) (ρ : ℝ → ℝ)
    (hρ : IntegrableOn ρ (Set.Ioc u v)) (hpos : ∀ x ∈ Set.Ioc u v, 0 ≤ ρ x) :
    (intervalDensityMeasure u v ρ).real Set.univ = ∫ x in Set.Ioc u v, ρ x := by
  have hp : ∀ᵐ x ∂volume.restrict (Set.Ioc u v), 0 ≤ ρ x :=
    ae_restrict_of_forall_mem measurableSet_Ioc hpos
  rw [Measure.real, intervalDensityMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hρ hp,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hp)]

theorem measurable_selectedPrimeLogDensity (P : PublishedProgressionInput) (Q q a : ℕ) :
    Measurable (selectedPrimeLogDensity P Q q a) := by
  unfold selectedPrimeLogDensity primeLogDensity
  fun_prop

theorem selectedPrimeLogDensity_nonneg (P : PublishedProgressionInput) (Q q a : ℕ)
    (u v : ℝ) (hu : 0 ≤ u) (x : ℝ) (hx : x ∈ Set.Ioc u v) :
    0 ≤ selectedPrimeLogDensity P Q q a x :=
  (primeLogDensity_bounds _ _ _ (Nat.cast_nonneg _) (pageCoefficient_abs_le_one _ _)
    (pageBeta_le_one _) (hu.trans hx.1.le)).1

theorem selectedPrimeLogDensity_integrable (P : PublishedProgressionInput) (Q q a : ℕ)
    (u v : ℝ) (hu : 0 < u) : IntegrableOn (selectedPrimeLogDensity P Q q a) (Set.Ioc u v) :=
  (continuousOn_primeLogDensity _ _ _ hu).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

noncomputable def primeGiantMeasure (P : PublishedProgressionInput) (Q q a : ℕ)
    (u v : ℝ) : Measure ℝ := intervalDensityMeasure u v (selectedPrimeLogDensity P Q q a)

theorem finite_primeGiantMeasure (P : PublishedProgressionInput) (Q q a : ℕ)
    (u v : ℝ) (hu : 0 < u) : IsFiniteMeasure (primeGiantMeasure P Q q a u v) :=
  finite_intervalDensityMeasure u v _ (selectedPrimeLogDensity_integrable P Q q a u v hu)
    (selectedPrimeLogDensity_nonneg P Q q a u v hu.le)

theorem primeGiantMeasure_integral (P : PublishedProgressionInput) (Q q a : ℕ)
    (u v : ℝ) (hu : 0 ≤ u) (f : ℝ → ℂ) :
    (∫ x, f x ∂primeGiantMeasure P Q q a u v) =
      ∫ x in Set.Ioc u v, f x * (selectedPrimeLogDensity P Q q a x : ℂ) :=
  intervalDensityMeasure_integral u v _ (measurable_selectedPrimeLogDensity P Q q a).aemeasurable
    (selectedPrimeLogDensity_nonneg P Q q a u v hu) f

theorem primeGiantMeasure_mass_le_two (P : PublishedProgressionInput) (Q q a : ℕ)
    (hq : 1 ≤ q) (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1) :
    (primeGiantMeasure P Q q a u v).real Set.univ ≤ 2 := by
  rw [primeGiantMeasure, intervalDensityMeasure_mass u v _
    (selectedPrimeLogDensity_integrable P Q q a u v (by linarith))
    (selectedPrimeLogDensity_nonneg P Q q a u v (by linarith))]
  apply (le_abs_self _).trans
  exact primeLogDensity_integral_abs_le_two _ _ _
    (by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q))
    (pageCoefficient_abs_le_one _ _) (pageBeta_le_one _) hu huv hshort

noncomputable def integerGiantMeasure (q : ℕ) (G u v : ℝ) : Measure ℝ :=
  intervalDensityMeasure u v (integerLogDensity q G)

theorem finite_integerGiantMeasure (q : ℕ) (G u v : ℝ) :
    IsFiniteMeasure (integerGiantMeasure q G u v) :=
  finite_intervalDensityMeasure u v _
    ((continuous_integerLogDensity q G).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
    (by intro x _; unfold integerLogDensity; positivity)

theorem integerGiantMeasure_integral (q : ℕ) (G u v : ℝ) (f : ℝ → ℂ) :
    (∫ x, f x ∂integerGiantMeasure q G u v) =
      ∫ x in Set.Ioc u v, f x * (integerLogDensity q G x : ℂ) :=
  intervalDensityMeasure_integral u v _ (continuous_integerLogDensity q G).measurable.aemeasurable
    (by intro x _; unfold integerLogDensity; positivity) f

theorem integerGiantMeasure_mass_le (q : ℕ) (hq : 0 < q) (J u v : ℝ)
    (huv : u ≤ v) (hshort : v ≤ u + 1) :
    (integerGiantMeasure q J u v).real Set.univ ≤ Real.exp (v - J) := by
  rw [integerGiantMeasure, intervalDensityMeasure_mass u v _
    ((continuous_integerLogDensity q J).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
    (by intro x _; unfold integerLogDensity; positivity)]
  exact (le_abs_self _).trans (integerLogDensity_integral_abs_le q hq u v J huv hshort)

end Ostmann

end OAI
