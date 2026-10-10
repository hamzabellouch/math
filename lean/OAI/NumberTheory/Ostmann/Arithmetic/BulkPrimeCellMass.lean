import OAI.NumberTheory.Ostmann.Arithmetic.BulkCellMixtures
import OAI.NumberTheory.Ostmann.Arithmetic.BulkLogSliceComparison

namespace OAI

/-! # Mass control for the normalized union of actual prime cells -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

noncomputable def bulkConstant {σ : Type*} (c : ℂ) : BulkIntegrand σ where
  toFun _ := c
  measurable := measurable_const
  bounded := ⟨‖c‖, norm_nonneg _, fun _ => le_rfl⟩

theorem bulkConstant_average_one {σ : Type*} [Fintype σ]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (i : σ) (x : σ → ℝ) :
    (bulkConstant (σ := σ) 1).average μ i x = (μ.real Set.univ : ℂ) := by
  change (∫ _t : ℝ, (1 : ℂ) ∂μ) = _
  simp only [integral_const, Complex.real_smul, mul_one]

theorem primeLogCell_page_mass_error (P : PublishedProgressionInput)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1) :
    |(primeLogCellMeasure q a u v).real Set.univ -
      (primeGiantMeasure P Q q a u v).real Set.univ| ≤ bulkPrimeErrorFactor P Q u := by
  rw [primeLogCellMeasure_mass, sum_primeLogCellSet_reciprocal,
    primeGiantMeasure, intervalDensityMeasure_mass u v _
      (selectedPrimeLogDensity_integrable P Q q a u v (by linarith))
      (selectedPrimeLogDensity_nonneg P Q q a u v (by linarith))]
  have h := P.uniform_log_interval hQ hq hqQ ha hu huv hshort
  exact h.trans (le_add_of_nonneg_right (by positivity : 0 ≤ 2 * Real.exp (-u)))

/-- If the original normalized prime law has mass at most one, the ideal
Page law has mass at most two once its derived interval error is at most one. -/
theorem PublishedProgressionInput.bulk_cell_page_mass_le_two
    (P : PublishedProgressionInput) {C : Type*} [Fintype C]
    (Q : ℕ) (hQ : 2 ≤ Q) (q a : C → ℕ) (u v : C → ℝ)
    (hq : ∀ c, 1 ≤ q c) (hqQ : ∀ c, q c ≤ Q) (ha : ∀ c, (a c).Coprime (q c))
    (hu : ∀ c, 1 ≤ u c) (huv : ∀ c, u c ≤ v c) (hshort : ∀ c, v c ≤ u c + 1)
    (Z : ℝ) (hZ : 0 ≤ Z)
    (hmass : (bulkCellMixture Z (fun c => primeLogCellMeasure (q c) (a c) (u c) (v c))).real Set.univ ≤ 1)
    (herror : Z * ∑ c, bulkPrimeErrorFactor P Q (u c) ≤ 1) :
    (bulkCellMixture Z (fun c => primeGiantMeasure P Q (q c) (a c) (u c) (v c))).real Set.univ ≤ 2 := by
  let μ := fun c => primeLogCellMeasure (q c) (a c) (u c) (v c)
  let ν := fun c => primeGiantMeasure P Q (q c) (a c) (u c) (v c)
  let _ : ∀ c, IsFiniteMeasure (ν c) := fun c =>
    finite_primeGiantMeasure P Q (q c) (a c) (u c) (v c) (by linarith [hu c])
  have hc (c : C) (x : Unit → ℝ) :
      ‖(bulkConstant (σ := Unit) 1).average (μ c) () x -
        (bulkConstant (σ := Unit) 1).average (ν c) () x‖ ≤ bulkPrimeErrorFactor P Q (u c) := by
    rw [bulkConstant_average_one, bulkConstant_average_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    exact primeLogCell_page_mass_error P hQ (hq c) (hqQ c) (ha c) (u c) (v c) (hu c) (huv c) (hshort c)
  have h := (bulkConstant (σ := Unit) 1).cellMixture_comparison Z hZ μ ν ()
    (fun c => bulkPrimeErrorFactor P Q (u c)) hc (fun _ => 0)
  rw [bulkConstant_average_one, bulkConstant_average_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at h
  have hh := (abs_le.mp (h.trans herror)).1
  change (bulkCellMixture Z μ).real Set.univ ≤ 1 at hmass
  change (bulkCellMixture Z ν).real Set.univ ≤ 2
  linarith

end Ostmann

end OAI
