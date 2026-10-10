import OAI.NumberTheory.Ostmann.Arithmetic.BulkProductMixtures

namespace OAI

/-! # Exact finite atomic product integrals for the original prime cells -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem bulk_pi_scaled_dirac {J : Type*} [Fintype J]
    (x : J → ℝ) (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) :
    Measure.pi (fun j => ENNReal.ofReal (w j) • Measure.dirac (x j)) =
      ENNReal.ofReal (∏ j, w j) • Measure.dirac x := by
  let _ : ∀ j, IsFiniteMeasure (ENNReal.ofReal (w j) • Measure.dirac (x j)) :=
    fun j => (Measure.dirac (x j)).smul_finite ENNReal.ofReal_ne_top
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.smul_apply, Measure.dirac_apply' _ (MeasurableSet.univ_pi hs),
    Measure.dirac_apply' _ (hs _), smul_eq_mul]
  rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => hw j), Finset.prod_mul_distrib]
  by_cases h : ∀ j, x j ∈ s j
  · simp [h]
  · have hex : ∃ j, x j ∉ s j := not_forall.mp h
    obtain ⟨j, hj⟩ := hex
    have hz : (∏ i, (s i).indicator (fun _ => (1 : ENNReal)) (x i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem hj _)
    change (∏ i, ENNReal.ofReal (w i)) *
        (Set.univ.pi s).indicator (fun _ => (1 : ENNReal)) x =
      (∏ i, ENNReal.ofReal (w i)) * ∏ i, (s i).indicator (fun _ => (1 : ENNReal)) (x i)
    rw [hz, Set.indicator_of_notMem (by simpa only [Set.mem_univ_pi] using h)]

theorem BulkIntegrand.integral_atomic_product {J A : Type*} [Fintype J] [Fintype A]
    (f : BulkIntegrand J) (x : J → A → ℝ) (w : J → A → ℝ)
    (hw : ∀ j a, 0 ≤ w j a) :
    (∫ y, f y ∂Measure.pi (fun j => ∑ a, ENNReal.ofReal (w j a) • Measure.dirac (x j a))) =
      ∑ a : J → A, ((∏ j, w j (a j) : ℝ) : ℂ) * f (fun j => x j (a j)) := by
  let _ : ∀ j a, IsFiniteMeasure (ENNReal.ofReal (w j a) • Measure.dirac (x j a)) :=
    fun j a => (Measure.dirac (x j a)).smul_finite ENNReal.ofReal_ne_top
  have he := f.integral_product_mixtures (fun _ => 1) (fun _ => zero_le_one)
    (fun j a => ENNReal.ofReal (w j a) • Measure.dirac (x j a))
  simp only [bulkCellMixture, ENNReal.ofReal_one, one_smul, Finset.prod_const_one,
    Complex.ofReal_one, one_mul] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro a _
  rw [bulk_pi_scaled_dirac (fun j => x j (a j)) (fun j => w j (a j)) (fun j => hw j (a j)),
    integral_smul_measure, ENNReal.toReal_ofReal (Finset.prod_nonneg fun j _ => hw j (a j)),
    integral_dirac, Complex.real_smul]

end Ostmann

end OAI
