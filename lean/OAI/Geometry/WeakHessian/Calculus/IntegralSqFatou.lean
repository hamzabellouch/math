import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology ENNReal

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma integral_sq_fatou {f : X → ℝ} (hf : AEStronglyMeasurable f m)
    {fs : ℕ → X → ℝ} (hfs : ∀ n, MemLp (fs n) 2 m)
    (hlim : ∀ᵐ x ∂m, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) {B : ℝ}
    (hB : ∀ n, (∫ x, (fs n x)^2 ∂m) ≤ B) :
    MemLp f 2 m ∧ (∫ x, (f x)^2 ∂m) ≤ B := by
  have H : (∫⁻ x, ENNReal.ofReal ((f x)^2) ∂m) ≤ ENNReal.ofReal B := by
    calc
      _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal ((fs n x)^2)) atTop ∂m := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with x hx
        exact ((ENNReal.continuous_ofReal.tendsto _).comp (hx.pow 2)).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal ((fs n x)^2) ∂m) atTop :=
        lintegral_liminf_le' (fun index => ENNReal.continuous_ofReal.measurable.comp_aemeasurable
          ((hfs index).aestronglyMeasurable.pow 2).aemeasurable)
      _ ≤ ENNReal.ofReal B := by
        apply liminf_le_of_frequently_le'
        apply Frequently.of_forall
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hfs n).integrable_sq (ae_of_all _ (fun x => sq_nonneg _))]
        exact ENNReal.ofReal_le_ofReal (hB n)
  have hi : Integrable (fun x => (f x)^2) m := by
    refine ⟨hf.pow 2, ?_⟩
    change (∫⁻ x, ‖(f x)^2‖ₑ ∂m) < ∞
    simp only [Real.enorm_eq_ofReal (sq_nonneg _)]
    exact H.trans_lt ENNReal.ofReal_lt_top
  refine ⟨(memLp_two_iff_integrable_sq hf).mpr hi, ?_⟩
  have hB0 : 0 ≤ B := (integral_nonneg (fun x => sq_nonneg (fs 0 x))).trans (hB 0)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun x => sq_nonneg _)) hi.1]
  simpa only [ENNReal.toReal_ofReal hB0] using ENNReal.toReal_mono ENNReal.ofReal_ne_top H

end WeakHessian

end
end InlinedFile0

end OAI
