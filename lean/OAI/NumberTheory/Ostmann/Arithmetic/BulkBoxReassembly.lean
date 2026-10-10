import OAI.NumberTheory.Ostmann.Arithmetic.BulkProductMixtures

namespace OAI

/-! # The harmonic box masses absorb the joint cell sum -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

/-- Reassembling boxes costs the product of their normalized masses. It does
not cost the number of boxes in the main term. -/
theorem bulk_box_sum_bound {J C : Type*} [Fintype J] [Fintype C]
    (Z : J → ℝ) (hZ : ∀ j, 0 ≤ Z j) (H : J → C → ℝ)
    (hH : ∀ j c, 0 ≤ H j c) (hmass : ∀ j, Z j * ∑ c, H j c ≤ 2)
    (B : ℝ) (hB : 0 ≤ B) (E : (J → C) → ℂ)
    (hE : ∀ c, ‖E c‖ ≤ B * ∏ j, H j (c j)) :
    ‖((∏ j, Z j : ℝ) : ℂ) * ∑ c, E c‖ ≤ B * 2 ^ Fintype.card J := by
  have hZp : 0 ≤ ∏ j, Z j := Finset.prod_nonneg fun j _ => hZ j
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hZp]
  calc
    _ ≤ (∏ j, Z j) * ∑ c : J → C, B * ∏ j, H j (c j) := by
      apply mul_le_mul_of_nonneg_left _ hZp
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => hE c)
    _ = B * ∏ j, (Z j * ∑ c, H j c) := by
      rw [← Finset.mul_sum, ← Fintype.prod_sum, Finset.prod_mul_distrib]
      ring
    _ ≤ B * 2 ^ Fintype.card J := by
      apply mul_le_mul_of_nonneg_left _ hB
      calc
        _ ≤ ∏ _j : J, (2 : ℝ) := Finset.prod_le_prod₀
          (fun j _ => mul_nonneg (hZ j) (Finset.sum_nonneg fun c _ => hH j c))
          (fun j _ => hmass j)
        _ = _ := by simp only [Finset.prod_const, Finset.card_univ]

/-- The same bound for the exact normalized product of cell measures. -/
theorem BulkIntegrand.integral_product_mixtures_bound {J C : Type*} [Fintype J] [Fintype C]
    (f : BulkIntegrand J) (Z : J → ℝ) (hZ : ∀ j, 0 ≤ Z j)
    (μ : J → C → Measure ℝ) [∀ j c, IsFiniteMeasure (μ j c)]
    (H : J → C → ℝ) (hH : ∀ j c, 0 ≤ H j c)
    (hmass : ∀ j, Z j * ∑ c, H j c ≤ 2)
    (B : ℝ) (hB : 0 ≤ B)
    (hbox : ∀ c : J → C,
      ‖∫ x, f x ∂Measure.pi (fun j => μ j (c j))‖ ≤ B * ∏ j, H j (c j)) :
    ‖∫ x, f x ∂Measure.pi (fun j => bulkCellMixture (Z j) (μ j))‖ ≤ B * 2 ^ Fintype.card J := by
  rw [f.integral_product_mixtures Z hZ μ]
  exact bulk_box_sum_bound Z hZ H hH hmass B hB _ hbox

end Ostmann

end OAI
