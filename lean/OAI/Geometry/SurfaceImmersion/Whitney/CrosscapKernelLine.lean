import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapKernelCapture

namespace OAI

/-! Explicit coordinates for the kernel line of a regular crosscap. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def tangentRayCoefficient (b : Bool) (x : Base) : ℝ := if b then x 1 else x 0

def tangentTransverseCoefficient (b : Bool) (t : ℝ) (x : Base) : ℝ :=
  if b then x 0-t*x 1 else x 1-t*x 0

lemma tangentRay_decomposition (b : Bool) (t : ℝ) (x : Base) :
    x = tangentTransverseCoefficient b t x • tangentRayVelocity b +
      tangentRayCoefficient b x • tangentRay b t := by
  cases b <;> ext i <;> fin_cases i <;>
    simp [tangentTransverseCoefficient,tangentRayCoefficient,tangentRayVelocity,tangentRay] <;> ring

lemma kernel_eq_tangentRay_line (L : Base →L[ℝ] ProjectionTarget 3)
    (b : Bool) (t : ℝ) (hz : L (tangentRay b t) = 0)
    (hv : L (tangentRayVelocity b) ≠ 0) (x : Base) :
    L x = 0 ↔ x = tangentRayCoefficient b x • tangentRay b t := by
  constructor
  · intro hx
    have h := congrArg L (tangentRay_decomposition b t x)
    simp only [hx,map_add,map_smul,hz,smul_zero,add_zero] at h
    have ht : tangentTransverseCoefficient b t x = 0 :=
      (smul_eq_zero.mp h.symm).resolve_right hv
    simpa only [ht,zero_smul,zero_add] using tangentRay_decomposition b t x
  · intro hx
    rw [hx,map_smul,hz,smul_zero]

lemma crosscap_kernel_line {f : Base → ProjectionTarget 3} (hf : ContDiff ℝ ∞ f)
    (b : Bool) (z : Base × ℝ) (hz : surfaceDirection f b z = 0)
    (hreg : Function.Injective (fderiv ℝ (surfaceDirection f b) z)) (x : Base) :
    fderiv ℝ f z.1 x = 0 ↔ x = tangentRayCoefficient b x • tangentRay b z.2 :=
  kernel_eq_tangentRay_line _ b z.2 hz (crosscap_transverse_derivative_ne_zero hf b z hreg) x

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
