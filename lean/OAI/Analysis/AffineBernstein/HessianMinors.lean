import Mathlib
import OAI.Analysis.AffineBernstein.SupportAnnulus
import OAI.Analysis.AffineBernstein.MatrixShiftDet

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open scoped Matrix

variable {n : ℕ}

lemma shiftedGradient_injOn_of_hessian_posSemidef {Ω : Set (Space n)}
    (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ∀ x ∈ Ω, ContDiffAt ℝ ∞ u x)
    (hp : ∀ x ∈ Ω, (hessian u x).PosSemidef) :
    Set.InjOn (fun x => gradient u x + x) Ω := by
  apply injOn_of_positive_derivative hcv
  · intro x hx
    exact ((contDiffAt_gradient (hu x hx)).differentiableAt (by simp)).add differentiableAt_id
  · intro x hx v hv
    change 0 < inner ℝ (fderiv ℝ (fun y => gradient u y + id y) x v) v
    rw [fderiv_fun_add ((contDiffAt_gradient (hu x hx)).differentiableAt (by simp))
      differentiableAt_id,fderiv_id]
    simp only [add_apply,ContinuousLinearMap.id_apply,inner_add_left,
      inner_fderiv_gradient (hu x hx)]
    exact add_pos_of_nonneg_of_pos (second_fderiv_nonneg (hu x hx) (hp x hx) v)
      (real_inner_self_pos.mpr hv)

/- One genuine change of variables for the shifted convex gradient bounds
all the large principal minors at once. This is an alternative proof of the
source principal-minor estimate, with every quantity the actual Hessian.
It does not posit any Hessian or determinant bound. -/
theorem lintegral_hessian_minors_le_ball {Ω : Set (Space n)}
    (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ∀ x ∈ Ω, ContDiffAt ℝ ∞ u x)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {D : Set (Space n)} (hD : MeasurableSet D) (hDO : D ⊆ Ω)
    {G R : ℝ} (hG : ∀ x ∈ D, ‖gradient u x‖ ≤ G)
    (hR : ∀ x ∈ D, ‖x‖ ≤ R) :
    (∫⁻ x in D, ENNReal.ofReal ((hessian u x).det * (1 + (hessian u x)⁻¹.trace))) ≤
      ((n:ℝ≥0∞)+1) * volume (Metric.closedBall (0:Space n) (G+R)) := by
  let F := fun x => gradient u x + x
  have hd (x : Space n) (hx : x ∈ D) : DifferentiableAt ℝ F x :=
    ((contDiffAt_gradient (hu x (hDO hx))).differentiableAt (by simp)).add differentiableAt_id
  have hi : Set.InjOn F D :=
    (shiftedGradient_injOn_of_hessian_posSemidef hcv hu (fun x hx => (hp x hx).posSemidef)).mono hDO
  have hj := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hD
    (fun x hx => (hd x hx).hasFDerivAt.hasFDerivWithinAt) hi (fun _ : Space n => (1:ℝ≥0∞))
  simp only [lintegral_const,Measure.restrict_apply_univ,mul_one,one_mul] at hj
  have himage : F '' D ⊆ Metric.closedBall 0 (G+R) := by
    rintro _ ⟨x,hx,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (norm_add_le _ _).trans (add_le_add (hG x hx) (hR x hx))
  calc
    _ ≤ ∫⁻ x in D, ((n:ℝ≥0∞)+1)*ENNReal.ofReal |(fderiv ℝ F x).det| := by
      apply setLIntegral_mono' hD
      intro x hx
      have hp' := hp x (hDO hx)
      have hdpos := (hp'.posSemidef.add Matrix.PosSemidef.one).det_nonneg
      rw [show F = (fun x => gradient u x+x) from rfl,
        det_fderiv_shiftedGradient (hu x (hDO hx)),abs_of_nonneg hdpos]
      have hc : ((n:ℝ≥0∞)+1) = ENNReal.ofReal ((n:ℝ)+1) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
        simp
      rw [hc,← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      simpa only [Fintype.card_fin] using det_mul_one_add_trace_inv_le hp'
    _ = ((n:ℝ≥0∞)+1) * ∫⁻ x in D, ENNReal.ofReal |(fderiv ℝ F x).det| := by
      rw [lintegral_const_mul']
      simp
    _ ≤ _ := by
      rw [← hj]
      exact mul_le_mul_right (measure_mono (μ := volume) himage) _

end AffineBernstein
end

end OAI
