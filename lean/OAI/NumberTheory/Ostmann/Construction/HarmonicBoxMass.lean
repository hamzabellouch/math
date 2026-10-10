import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OAI.NumberTheory.Ostmann.Supply.PrimeSubsetMass
import OAI.NumberTheory.Ostmann.Arithmetic.BulkProductMixtures

namespace OAI

/-! # The true harmonic mass of the reassembled bulk boxes -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem pageAtModulus_one (z : Option PrimitiveRealZero) : pageAtModulus 1 z = none := by
  cases z with
  | none => rfl
  | some e =>
    simp [pageAtModulus, e.modulus_ne_one]

theorem selectedPrimeLogDensity_one (P : PublishedProgressionInput) (Q a : ℕ) (x : ℝ) :
    selectedPrimeLogDensity P Q 1 a x = x⁻¹ := by
  simp [selectedPrimeLogDensity, primeLogDensity, pageAtModulus_one, pageCoefficient]

theorem primeGiantMeasure_one_mass (P : PublishedProgressionInput) (Q a : ℕ)
    (u v : ℝ) (hu : 0 < u) :
    (primeGiantMeasure P Q 1 a u v).real Set.univ = ∫ x in Set.Ioc u v, (x : ℝ)⁻¹ := by
  rw [primeGiantMeasure, intervalDensityMeasure_mass u v _
    (selectedPrimeLogDensity_integrable P Q 1 a u v hu)
    (selectedPrimeLogDensity_nonneg P Q 1 a u v hu.le)]
  simp only [selectedPrimeLogDensity_one]

theorem bulkCellMixture_mass {C : Type*} [Fintype C]
    (Z : ℝ) (hZ : 0 ≤ Z) (μ : C → Measure ℝ) [∀ c, IsFiniteMeasure (μ c)] :
    (bulkCellMixture Z μ).real Set.univ = Z * ∑ c, (μ c).real Set.univ := by
  have h := (bulkConstant (σ := Unit) 1).average_cellMixture Z hZ μ () (fun _ => 0)
  simp only [bulkConstant_average_one, ← Complex.ofReal_sum, ← Complex.ofReal_mul] at h
  exact_mod_cast h

/-- Comparison with the modulus-one prime law bounds the sum of the real
harmonic box masses, with the original normalization and no count of boxes. -/
theorem PublishedProgressionInput.harmonic_box_mass_le_two
    (P : PublishedProgressionInput) {C : Type*} [Fintype C]
    (Q : ℕ) (hQ : 2 ≤ Q) (u v : C → ℝ)
    (hu : ∀ c, 1 ≤ u c) (huv : ∀ c, u c ≤ v c) (hshort : ∀ c, v c ≤ u c + 1)
    (Z : ℝ) (hZ : 0 ≤ Z)
    (hmass : (bulkCellMixture Z (fun c => primeLogCellMeasure 1 0 (u c) (v c))).real Set.univ ≤ 1)
    (herror : Z * ∑ c, bulkPrimeErrorFactor P Q (u c) ≤ 1) :
    Z * ∑ c, ∫ x in Set.Ioc (u c) (v c), (x : ℝ)⁻¹ ≤ 2 := by
  let _ : ∀ c, IsFiniteMeasure (primeGiantMeasure P Q 1 0 (u c) (v c)) :=
    fun c => finite_primeGiantMeasure P Q 1 0 (u c) (v c) (lt_of_lt_of_le zero_lt_one (hu c))
  have h := P.bulk_cell_page_mass_le_two Q hQ (fun _ => 1) (fun _ => 0) u v
    (fun _ => le_refl _) (fun _ => by omega) (fun _ => by simp) hu huv hshort Z hZ hmass herror
  rw [bulkCellMixture_mass Z hZ] at h
  simpa only [primeGiantMeasure_one_mass P Q 0 _ _ (lt_of_lt_of_le zero_lt_one (hu _))] using h

theorem harmonic_box_mass_log (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) :
    (∫ x in Set.Ioc u v, (x : ℝ)⁻¹) = Real.log (v / u) := by
  rw [← intervalIntegral.integral_of_le huv, integral_inv_of_pos hu (hu.trans_le huv)]

end Ostmann

end OAI
