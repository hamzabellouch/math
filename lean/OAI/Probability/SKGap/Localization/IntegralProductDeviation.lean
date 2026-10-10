import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
namespace SKGap
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma integral_product_deviation {X Y : Ω → ℝ} {C T : ℝ}
    (hX : Integrable X μ) (hY : AEStronglyMeasurable Y μ)
    (hC : ∀ᵐ x ∂μ, ‖Y x‖ ≤ C)
    (hT : (∫ x, |X x-∫ y, X y ∂μ| ∂μ) ≤ T) :
    |(∫ x, X x*Y x ∂μ)-(∫ x, X x ∂μ)*(∫ x, Y x ∂μ)| ≤ C*T := by
  have hC0 : 0 ≤ C := by
    obtain ⟨x,hx⟩ := hC.exists
    exact (norm_nonneg _).trans hx
  have hYi : Integrable Y μ := (integrable_const C).mono' hY hC
  have hXY : Integrable (fun x => X x*Y x) μ := by
    simpa only [mul_comm] using hX.bdd_mul hY hC
  have hcenter : Integrable (fun x => X x-∫ y, X y ∂μ) μ := hX.sub (integrable_const _)
  have hci : Integrable (fun x => (X x-∫ y, X y ∂μ)*Y x) μ := by
    simpa only [mul_comm] using hcenter.bdd_mul hY hC
  have he : (∫ x, X x*Y x ∂μ)-(∫ x, X x ∂μ)*(∫ x, Y x ∂μ) =
      ∫ x, (X x-∫ y, X y ∂μ)*Y x ∂μ := by
    simp_rw [sub_mul]
    rw [integral_sub hXY (hYi.const_mul _),integral_const_mul]
  rw [he]
  calc
    _ ≤ ∫ x, ‖(X x-∫ y, X y ∂μ)*Y x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, C*|X x-∫ y, X y ∂μ| ∂μ := by
      apply integral_mono_ae hci.norm (hcenter.norm.const_mul C)
      filter_upwards [hC] with x hx
      simpa only [norm_mul,Real.norm_eq_abs,mul_comm] using
        mul_le_mul_of_nonneg_left hx (norm_nonneg (X x-∫ y, X y ∂μ))
    _ = C*(∫ x, |X x-∫ y, X y ∂μ| ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hT hC0

lemma integral_loop_deviation {X Y Z V : Ω → ℝ} {r C T B E : ℝ}
    (hr : 0 ≤ r) (hX : Integrable X μ) (hY : AEStronglyMeasurable Y μ)
    (hC : ∀ᵐ x ∂μ, ‖Y x‖ ≤ C)
    (hZ : Integrable Z μ) (hB : ∀ᵐ x ∂μ, ‖Z x‖ ≤ B)
    (hT : (∫ x, |X x-∫ y, X y ∂μ| ∂μ) ≤ T)
    (hE : |(∫ x, V x ∂μ)-r*(∫ x, X x*Y x+Z x ∂μ)| ≤ E) :
    |(∫ x, V x ∂μ)-r*(∫ x, X x ∂μ)*(∫ x, Y x ∂μ)| ≤ E+r*(C*T+B) := by
  have hXY : Integrable (fun x => X x*Y x) μ := by
    simpa only [mul_comm] using hX.bdd_mul hY hC
  have hbound := integral_product_deviation hX hY hC hT
  have hb : |∫ x, Z x ∂μ| ≤ B := by
    exact (norm_integral_le_integral_norm _).trans ((integral_mono_ae hZ.norm (integrable_const B) hB).trans_eq (by simp))
  have he : (∫ x, V x ∂μ)-r*(∫ x, X x ∂μ)*(∫ x, Y x ∂μ) =
      ((∫ x, V x ∂μ)-r*(∫ x, X x*Y x+Z x ∂μ))+
      r*((∫ x, X x*Y x ∂μ)-(∫ x, X x ∂μ)*(∫ x, Y x ∂μ)+(∫ x, Z x ∂μ)) := by
    rw [integral_add hXY hZ]; ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hE (by
    rw [abs_mul,abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hbound hb)) hr))

end SKGap

end
end
end
end
end
end

end OAI
