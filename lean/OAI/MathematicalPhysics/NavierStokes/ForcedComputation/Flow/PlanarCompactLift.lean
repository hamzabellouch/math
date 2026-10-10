import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.TriangularFluid
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.CompactPlanarFlow

namespace OAI

/-! A compact vertical cutoff of a planar incompressible processor. Its
horizontal trajectories at a cutoff plateau remain exact, and the cutoff
introduces no divergence because the lifted field has zero third component. -/

noncomputable section
namespace ForcedComputation.CompactLift
open ShearFlows VelocityDetector Set
open scoped ContDiff BigOperators

def spatial (χ : ℝ → ℝ) (a : Plane → Plane) (x : Space) : Space :=
  χ (x 2) • triangularLift a (fun _ => 0) x

def velocity (χ : ℝ → ℝ) (V : ℝ → Plane → Plane) : Velocity :=
  fun y => spatial χ (V y.1) y.2

theorem spatial_smooth {χ : ℝ → ℝ} {a : Plane → Plane}
    (hχ : ContDiff ℝ ∞ χ) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (spatial χ a) :=
  (hχ.comp (contDiff_apply ℝ ℝ (2 : Fin 3))).smul
    (triangularLift_smooth ha contDiff_const)

theorem velocity_smooth {χ : ℝ → ℝ} {V : ℝ → Plane → Plane}
    (hχ : ContDiff ℝ ∞ χ) (hV : ContDiff ℝ ∞ (Function.uncurry V)) :
    ContDiff ℝ ∞ (velocity χ V) := by
  have hi : ContDiff ℝ ∞ (fun y : SpaceTime => (y.1, horizontalLinear y.2)) :=
    contDiff_fst.prodMk (horizontalLinear.contDiff.comp contDiff_snd)
  have hW : ContDiff ℝ ∞ (fun y : SpaceTime => planeInclusion (V y.1 (horizontalLinear y.2))) :=
    planeInclusion.contDiff.comp (hV.comp hi)
  have he : velocity χ V = fun y => χ (y.2 2) • planeInclusion (V y.1 (horizontalLinear y.2)) := by
    funext y
    simp [velocity, spatial, triangularLift]
  rw [he]
  exact (hχ.comp ((contDiff_apply ℝ ℝ (2 : Fin 3)).comp contDiff_snd)).smul hW

theorem spatial_third (χ : ℝ → ℝ) (a : Plane → Plane) (x : Space) :
    spatial χ a x 2 = 0 := by
  simp [spatial, triangularLift_eq, atHeight]

theorem spatial_atHeight {χ : ℝ → ℝ} (a : Plane → Plane) {z : ℝ}
    (hz : χ z = 1) (x : Plane) : spatial χ a (atHeight x z) = planeInclusion (a x) := by
  simp only [spatial, triangularLift, horizontalLinear_eq, atHeight_horizontal,
    zero_smul, add_zero]
  change χ z • planeInclusion (a x) = _
  rw [hz, one_smul]

theorem height_fderiv {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (x : Space) (j : Fin 3) :
    fderiv ℝ (fun y : Space => χ (y 2)) x (basis j) = deriv χ (x 2) * basis j 2 := by
  have hd := ((hχ.differentiable (by simp) (x 2)).hasDerivAt).comp_hasFDerivAt x
    (ContinuousLinearMap.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt
  simpa only [Function.comp_def, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul] using
    congrArg (fun L => L (basis j)) hd.fderiv

theorem spatial_divergence {χ : ℝ → ℝ} {a : Plane → Plane}
    (hχ : ContDiff ℝ ∞ χ) (ha : ContDiff ℝ ∞ a) (x : Space) :
    divergence (spatial χ a) x = χ (x 2) * PlanarHamiltonian.divergence a (horizontal x) := by
  let W := triangularLift a (fun _ => 0)
  have hw : ContDiff ℝ ∞ W := triangularLift_smooth ha contDiff_const
  have hc : ContDiff ℝ ∞ (fun y : Space => χ (y 2)) := hχ.comp (contDiff_apply ℝ ℝ (2 : Fin 3))
  have hd (j : Fin 3) : derivative (spatial χ a) j x j =
      χ (x 2) * derivative W j x j +
        (deriv χ (x 2) * basis j 2) * W x j := by
    unfold derivative
    rw [show spatial χ a = (fun y : Space => χ (y 2) • W y) from rfl,
      fderiv_fun_smul (hc.differentiable (by simp) x) (hw.differentiable (by simp) x)]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      height_fderiv hχ]
  have hz : W x 2 = 0 := by simp [W, triangularLift_eq, atHeight]
  have he : divergence (spatial χ a) x = χ (x 2) * divergence W x := by
    rw [divergence, divergence, Fin.sum_univ_three, Fin.sum_univ_three]
    rw [hd, hd, hd]
    simp only [basis, Pi.single_eq_of_ne (by decide : (2 : Fin 3) ≠ 0),
      Pi.single_eq_of_ne (by decide : (2 : Fin 3) ≠ 1), Pi.single_eq_same,
      hz, mul_zero, add_zero]
    ring
  rw [he, triangularLift_divergence ha contDiff_const]

theorem atHeight_hasDerivAt {γ : ℝ → Plane} {v : Plane} {t z : ℝ}
    (hγ : HasDerivAt γ v t) :
    HasDerivAt (fun s => atHeight (γ s) z) (planeInclusion v) t := by
  have hd := (planeInclusion.hasFDerivAt.comp_hasDerivAt t hγ).add_const (z • basis 2)
  convert hd using 1
  · funext s
    ext j
    fin_cases j <;> simp [planeInclusion, atHeight, basis]

theorem trajectory_atHeight {χ : ℝ → ℝ} {V : ℝ → Plane → Plane}
    {γ : ℝ → Plane} {a t z : ℝ} (hz : χ z = 1)
    (hγ : HasDerivAt γ (V (a + t) (γ t)) t) :
    HasDerivAt (fun s => atHeight (γ s) z)
      (velocity χ V (a + t, atHeight (γ t) z)) t := by
  simpa only [velocity, spatial_atHeight _ hz] using atHeight_hasDerivAt (z := z) hγ

end ForcedComputation.CompactLift

end

end OAI
