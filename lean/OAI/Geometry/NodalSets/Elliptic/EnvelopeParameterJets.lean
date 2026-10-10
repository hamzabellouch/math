import OAI.Geometry.NodalSets.Charts.LocalMetricJetContinuityLemmas
import OAI.Geometry.NodalSets.Elliptic.CorrugationEnvelopeJets
import OAI.Geometry.NodalSets.Elliptic.CorrugationLocalHessian

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section

lemma metricGradient_const_smul (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (f : Coord → ℝ) (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : Coord) :
    metricGradient g (t • f) x = t • metricGradient g f x := by
  simp only [metricGradient, fderiv_const_smul (hf.differentiable (by simp) x), map_smul]

lemma sourceHessian_const_smul (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (f : Coord → ℝ) (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : Coord) :
    sourceHessian g (t • f) x = t • sourceHessian g f x := by
  ext u v
  simp only [sourceHessian, sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, smul_apply, smul_eq_mul]
  rw [show t • f = (fun z ↦ t*f z) from rfl, scalar_const_mul_second t f hf]
  rw [fderiv_const_mul (hf.differentiable (by simp) x)]
  simp only [smul_apply, smul_eq_mul]
  ring

lemma envelope_parameter_jets (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (S f : Coord → ℝ) {x : Coord} (hS : ContDiffAt ℝ ∞ S x)
    (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    metricGradient g (S+t • f) x = metricGradient g S x + t • metricGradient g f x ∧
    sourceHessian g (S+t • f) x = sourceHessian g S x + t • sourceHessian g f x := by
  constructor
  · rw [metricGradient_add g S (t • f) (hS.differentiableAt (by simp))
      ((contDiff_const.smul hf).differentiable (by simp) x), metricGradient_const_smul g f hf]
  · ext u v
    rw [sourceHessian_add_at g S (t • f) hS (contDiff_const.smul hf).contDiffAt,
      sourceHessian_const_smul g f hf]
    rfl

end
end Yau.Geometry

end OAI
