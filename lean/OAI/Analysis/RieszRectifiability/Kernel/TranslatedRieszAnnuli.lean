import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.BlowupMeasure
import OAI.Analysis.RieszRectifiability.Kernel.NormalAnnularKernel

namespace OAI

/-!
Translation identifies centered annular Riesz integrals for the unit-scale blowup measure
with annular integrals around the original center, without changing the hard cutoff.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem translated_riesz_annulus_integral {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (ε R : ℝ) :
    (∫ x in ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}, kernel n x 0 ∂blowupMeasure n μ a 1) =
      ∫ y in ball a R ∩ {y | ε < dist y a}, kernel n y a ∂μ := by
  have : IsBoundedSMul ℝ (Ambient d) := NormedSpace.toIsBoundedSMul
  have : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  have : MeasurableSMul₂ ℝ (Ambient d) := ContinuousSMul.measurableSMul₂
  simp only [blowupMeasure, one_pow, inv_one, ENNReal.ofReal_one, one_smul]
  rw [setIntegral_map
    (measurableSet_ball.inter (measurableSet_lt measurable_const continuous_norm.measurable))
    (show AEStronglyMeasurable (fun x : Ambient d => kernel n x 0)
      (μ.map (fun y => y - a)) by unfold kernel; fun_prop) (by fun_prop)]
  have heq : (fun y : Ambient d => y - a) ⁻¹'
      (ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}) = ball a R ∩ {y | ε < dist y a} := by
    ext y
    simp only [mem_preimage, mem_inter_iff, mem_ball, mem_ofPred_eq, dist_eq_norm, sub_zero]
  rw [heq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by simp only [kernel, sub_zero]

end

end RieszRectifiability

end OAI
