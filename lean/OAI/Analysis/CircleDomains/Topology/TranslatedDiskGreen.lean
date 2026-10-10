import OAI.Analysis.CircleDomains.Topology.RoundDiskGreenProof
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Group.Integral

namespace OAI

/-! Translation of the proved round-disk Green identity to any center. -/
open Set Function MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma unitCircleParam_translate (c : ℂ) (R t : ℝ) :
    unitCircleParam c R t = c + unitCircleParam 0 R t := by
  simp only [unitCircleParam,circleMap,zero_add]

lemma planarFormIntegral_circle_translate (c : ℂ) (R : ℝ) (P Q : ℂ → ℝ) :
    planarFormIntegral P Q (unitCircleParam c R) =
      planarFormIntegral (fun z => P (c+z)) (fun z => Q (c+z)) (unitCircleParam 0 R) := by
  have heq : unitCircleParam c R = (fun t => c + unitCircleParam 0 R t) :=
    funext (unitCircleParam_translate c R)
  have hd (t : ℝ) : deriv (unitCircleParam c R) t = deriv (unitCircleParam 0 R) t := by
    rw [heq,deriv_const_add]
  unfold planarFormIntegral
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [unitCircleParam_translate,hd]

lemma integral_translated_ball (c : ℂ) (R : ℝ) (q : ℂ → ℝ) :
    (∫ z in ball c R, q z) = ∫ z in ball (0 : ℂ) R, q (c+z) := by
  have hm : MeasurePreserving (fun z : ℂ => c+z) volume volume :=
    measurePreserving_add_left volume c
  have he : MeasurableEmbedding (fun z : ℂ => c+z) :=
    (Homeomorph.addLeft c).measurableEmbedding
  have hb : (fun z : ℂ => c+z) ⁻¹' ball c R = ball 0 R := by
    ext z
    simp only [mem_preimage,mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero]
  have h := hm.setIntegral_preimage_emb he q (ball c R)
  rw [hb] at h
  exact h.symm

lemma translated_disk_green {P Q : ℂ → ℝ}
    (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    planarFormIntegral P Q (unitCircleParam c R) =
      ∫ z in ball c R, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
  rw [planarFormIntegral_circle_translate]
  have hPc : ContDiff ℝ ∞ (fun z => P (c+z)) := hP.comp (contDiff_const.add contDiff_id)
  have hQc : ContDiff ℝ ∞ (fun z => Q (c+z)) := hQ.comp (contDiff_const.add contDiff_id)
  rw [roundDiskGreen hPc hQc hR,integral_translated_ball c R
    (fun z => (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I)]
  apply setIntegral_congr_fun isOpen_ball.measurableSet
  intro z _
  dsimp only
  rw [fderiv_comp_add_left,fderiv_comp_add_left]

end CircleDomainRigidity

end

end OAI
