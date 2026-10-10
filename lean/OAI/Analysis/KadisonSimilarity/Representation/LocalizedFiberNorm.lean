import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

/-! Localized quadratic estimates determine the essential bound of an
operator field. Countably many vector tests suffice for the common null set. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter
open scoped ENNReal Topology

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (T : Ω → H →L[ℂ] H) {C : ℝ} (hC : 0 ≤ C)

include hC in
omit [CompleteSpace H] in
theorem ae_operator_norm_le_of_local_energy
    (hmeas : ∀ x : H, AEMeasurable (fun a => ENNReal.ofReal (‖T a x‖ ^ 2)) μ)
    (henergy : ∀ (x : H) (s : Set Ω), MeasurableSet s → μ s < ∞ →
      ∫⁻ a in s, ENNReal.ofReal (‖T a x‖ ^ 2) ∂μ ≤
        ∫⁻ _ in s, ENNReal.ofReal ((C * ‖x‖) ^ 2) ∂μ) :
    ∀ᵐ a ∂μ, ‖T a‖ ≤ C := by
  let d : ℕ → H := TopologicalSpace.denseSeq H
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq H
  have htest (n : ℕ) : ∀ᵐ a ∂μ, ‖T a (d n)‖ ≤ C * ‖d n‖ := by
    have h := ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ (hmeas (d n)) (henergy (d n))
    filter_upwards [h] with a ha
    have hs : ‖T a (d n)‖ ^ 2 ≤ (C * ‖d n‖) ^ 2 :=
      (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp ha
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp hs
  filter_upwards [eventually_countable_forall.mpr htest] with a ha
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  exact hd.induction_on x (isClosed_le (by fun_prop) (by fun_prop)) ha

end KadisonSimilarity

end

end OAI
