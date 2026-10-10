import OAI.Geometry.Relativity.CKS.SchwarzschildEnd
import OAI.Geometry.Relativity.CKS.SchwarzschildRoundMetric
import OAI.Geometry.Relativity.CKS.RiemannianContraction

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSReplacementCompleteness
open scoped ContDiff Topology ENNReal
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma velocity_abs_bound {m r : ℝ} (hr : 0 ≤ r) : |velocity m r| ≤ r+1 := by
  have h0 := Real.smoothTransition.nonneg (r-2*m-1)
  have h1 := Real.smoothTransition.le_one (r-2*m-1)
  have hl : -1 ≤ velocity m r := by
    unfold velocity
    nlinarith
  have hu : velocity m r ≤ r := by
    unfold velocity
    nlinarith
  exact abs_le.mpr ⟨by linarith,by linarith⟩
lemma lapseSquared_bound {m r : ℝ} (hm : 0 < m) (hr : 2*m ≤ r) :
    lapseSquared m r ≤ (r+2)^2 := by
  have hp : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hv := (sq_le_sq₀ (abs_nonneg (velocity m r)) (by linarith : 0 ≤ r+1)).mpr
    (velocity_abs_bound hp.le)
  rw [sq_abs] at hv
  have h := div_nonneg (by positivity : 0 ≤ 2*m) hp.le
  unfold lapseSquared
  nlinarith

def logRadius (m : ℝ) (p : Exterior) : ℝ := Real.log (radius m p+2)
lemma logRadius_smooth {m : ℝ} (hm : 0 < m) : ContMDiff I3 𝓘(ℝ,ℝ) ∞ (logRadius m) := by
  intro p
  show ContMDiffAt I3 𝓘(ℝ,ℝ) ∞ (Real.log ∘ fun q : Exterior => radius m q+2) p
  exact (Real.contDiffAt_log.mpr (ne_of_gt (by linarith [radius_pos hm p] : 0 < radius m p+2))).comp_contMDiffAt (f := fun q : Exterior => radius m q+2)
    ((radius_smooth m p).add contMDiffAt_const)
lemma mfderiv_logRadius {m : ℝ} (hm : 0 < m) (p : Exterior) :
    mfderiv I3 𝓘(ℝ,ℝ) (logRadius m) p = (radius m p+2)⁻¹ • firstCoordinate := by
  have hh := (((radius_smooth m p).mdifferentiableAt (by simp)).hasMFDerivAt).add
    (hasMFDerivAt_const (I := I3) (I' := 𝓘(ℝ,ℝ)) (2:ℝ) p)
  rw [mfderiv_radius] at hh
  have hl := (Real.hasDerivAt_log (ne_of_gt (by linarith [radius_pos hm p] : 0 < radius m p+2))).hasFDerivAt
  have he := (hl.hasMFDerivAt.comp p hh).mfderiv
  change mfderiv I3 𝓘(ℝ,ℝ) (logRadius m) p = _ at he
  rw [he]
  apply ContinuousLinearMap.ext
  intro v
  change (firstCoordinate v + 0) * ((radius m p+2)⁻¹) = (radius m p+2)⁻¹ * firstCoordinate v
  ring
lemma logRadius_derivative_bound {m : ℝ} (hm : 0 < m) (p : Exterior) (v : E3) :
    ‖mfderiv I3 𝓘(ℝ,ℝ) (logRadius m) p v‖ ≤
      tangentNorm I3 (smoothMetric hm).toContinuousRiemannianMetric p v := by
  rw [mfderiv_logRadius hm]
  rw [norm_tangentSpace_vectorSpace]
  change |(radius m p+2)⁻¹ * v 0| ≤ Real.sqrt (metricInner m p v v)
  have hr : 0 < radius m p+2 := by linarith [radius_pos hm p]
  have he : (radius m p+2)⁻¹ * v 0 = v 0/(radius m p+2) := by ring
  rw [he,← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  rw [div_pow,metricInner_quad hm]
  have h := div_le_div_of_nonneg_left (sq_nonneg (v 0))
    (lapseSquared_pos hm (radius_ge m p)) (lapseSquared_bound hm (radius_ge m p))
  have hnn : 0 ≤ (radius m p)^2 * ‖ambientDerivative directionAmbient p v‖^2 := by positivity
  linarith
lemma logRadius_sublevel_compact {m : ℝ} (hm : 0 < m) (c : ℝ) :
    IsCompact {p : Exterior | logRadius m p ≤ c} := by
  have he : {p : Exterior | logRadius m p ≤ c} = {p | radius m p ≤ Real.exp c-2} := by
    ext p
    simp only [mem_ofPred_eq,logRadius]
    rw [Real.log_le_iff_le_exp (by linarith [radius_pos hm p])]
    constructor <;> intro h <;> linarith
  rw [he]
  exact radius_sublevel_compact m _

theorem source_complete {m : ℝ} (hm : 0 < m) :
    IsComplete I3 (smoothMetric hm).toContinuousRiemannianMetric := by
  let g := (smoothMetric hm).toContinuousRiemannianMetric
  let : EMetricSpace Exterior := metricSpace I3 g
  apply complete_of_proper_scalar (f := logRadius m)
  · exact logRadius_sublevel_compact hm
  · intro p q
    exact scalar_edist_le_metricEDist g ((logRadius_smooth hm).of_le (by simp))
      (logRadius_derivative_bound hm) p q
end CKSSchwarzschild

end

end OAI
