import OAI.Geometry.SurfaceImmersion.Primitive.VelocityCoordinateData

namespace OAI

/-! At zero amplitude the radial velocity has the original value and
first derivative, without an extra exterior-neighborhood hypothesis. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma velocityRadius_normalize_jet {v : E → Vec} {a : E → ℝ} {x : E}
    (hv : ContDiffAt ℝ ∞ v x) (ha : ContDiffAt ℝ ∞ a x)
    (hn : v x ≠ 0) (hax : a x = 0) :
    velocityRadius (v x) (a x) • normalize (v x) = v x ∧
      fderiv ℝ (fun y => velocityRadius (v y) (a y) • normalize (v y)) x = fderiv ℝ v x := by
  have hs : ContDiffAt ℝ ∞ (fun y => v y ⬝ᵥ v y) x :=
    ContDiffAt.sum (fun i _ => (contDiffAt_pi.mp hv i).mul (contDiffAt_pi.mp hv i))
  have ha2 : HasFDerivAt (fun y => a y^2) (0 : E →L[ℝ] ℝ) x := by
    simpa [hax] using (ha.differentiableAt (by simp)).hasFDerivAt.pow 2
  have hspos : 0 < v x ⬝ᵥ v x := dot_self_pos hn
  have hrad := (hs.differentiableAt (by simp)).hasFDerivAt.add ha2
  have hrad' := hrad.sqrt (by simpa [hax] using hspos.ne')
  have hnorm := (hs.differentiableAt (by simp)).hasFDerivAt.sqrt hspos.ne'
  have hunit := (normalize_smoothAt hv hn).differentiableAt (by simp)
  constructor
  · simpa only [velocityRadius,hax,zero_pow (by decide : 2 ≠ 0),add_zero] using norm_smul_normalize hn
  · have hsame : fderiv ℝ (fun y => velocityRadius (v y) (a y) • normalize (v y)) x =
        fderiv ℝ (fun y => Real.sqrt (v y ⬝ᵥ v y) • normalize (v y)) x := by
      change fderiv ℝ ((fun y => velocityRadius (v y) (a y)) • (fun y => normalize (v y))) x =
        fderiv ℝ ((fun y => Real.sqrt (v y ⬝ᵥ v y)) • (fun y => normalize (v y))) x
      calc
        _ = _ := (hrad'.smul hunit.hasFDerivAt).fderiv
        _ = _ := by
          simpa [hax,velocityRadius] using (hnorm.smul hunit.hasFDerivAt).fderiv.symm
    have he : (fun y => Real.sqrt (v y ⬝ᵥ v y) • normalize (v y)) =ᶠ[𝓝 x] v := by
      filter_upwards [hv.continuousAt.eventually_ne hn] with y hy
      exact norm_smul_normalize hy
    exact hsame.trans he.fderiv_eq

end ClosedSurfaceR4.VelocityFrame

end

end OAI
