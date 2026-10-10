import OAI.Geometry.NodalSets.Elliptic.CorrugationPeriodicCell

namespace OAI

namespace Yau.Geometry
open Real Set
open scoped ContDiff
noncomputable section

def planeRadialCovector (z : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  z.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + z.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

lemma planeRadialCovector_apply (z v : ℝ × ℝ) :
    planeRadialCovector z v = z.1*v.1+z.2*v.2 := rfl

lemma corrugationDiskWell_hasFDerivAt (a R : ℝ) (z : ℝ × ℝ) :
    HasFDerivAt (corrugationDiskWell a R)
      ((a*expNegInvGlue (R^2-z.1^2-z.2^2)) • planeRadialCovector z) z := by
  have hd := ((hasFDerivAt_const (R^2) z).sub
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.pow 2)).sub
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.pow 2)
  have h := ((flatPrimitive_hasDerivAt (R^2-z.1^2-z.2^2)).comp_hasFDerivAt z hd).const_mul (-(a/2))
  change HasFDerivAt (corrugationDiskWell a R) _ z at h
  convert! h using 1
  ext <;> simp [planeRadialCovector] <;> ring

lemma corrugationDiskWell_fderiv (a R : ℝ) (z v : ℝ × ℝ) :
    fderiv ℝ (corrugationDiskWell a R) z v =
      a*expNegInvGlue (R^2-z.1^2-z.2^2)*(z.1*v.1+z.2*v.2) := by
  rw [(corrugationDiskWell_hasFDerivAt a R z).fderiv]
  rfl

lemma corrugationDiskWell_direction_hasFDerivAt (a R : ℝ) (z v : ℝ × ℝ) :
    HasFDerivAt (fun x ↦ fderiv ℝ (corrugationDiskWell a R) x v)
      ((a*expNegInvGlue (R^2-z.1^2-z.2^2)) • planeRadialCovector v -
        (2*a*((R^2-z.1^2-z.2^2)⁻¹)^2*expNegInvGlue (R^2-z.1^2-z.2^2)*
          (z.1*v.1+z.2*v.2)) • planeRadialCovector z) z := by
  have hd := ((hasFDerivAt_const (R^2) z).sub
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.pow 2)).sub
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.pow 2)
  have h := (((expNegInvGlue_hasDerivAt (R^2-z.1^2-z.2^2)).comp_hasFDerivAt z hd).const_mul a).mul
    (((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.mul_const v.1).add
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.mul_const v.2))
  have he : (fun x ↦ fderiv ℝ (corrugationDiskWell a R) x v) =
      (fun x : ℝ × ℝ ↦ a*expNegInvGlue (R^2-x.1^2-x.2^2)*(x.1*v.1+x.2*v.2)) :=
    funext (fun x ↦ corrugationDiskWell_fderiv a R x v)
  rw [he]
  convert! h using 1
  ext <;> simp [planeRadialCovector] <;> ring

lemma corrugationDiskWell_second (a R : ℝ) (z u v : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (corrugationDiskWell a R)) z u v =
      a*expNegInvGlue (R^2-z.1^2-z.2^2)*(u.1*v.1+u.2*v.2) -
        2*a*((R^2-z.1^2-z.2^2)⁻¹)^2*expNegInvGlue (R^2-z.1^2-z.2^2)*
          (z.1*u.1+z.2*u.2)*(z.1*v.1+z.2*v.2) := by
  have hd := ((corrugationDiskWell_smooth a R).fderiv_right (m := ∞) (by simp)).differentiable (by simp) z
  have he := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ ↦ L u)
    (hd.hasFDerivAt.clm_apply (hasFDerivAt_const v z)).fderiv
  simp only [ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply] at he
  rw [← he,(corrugationDiskWell_direction_hasFDerivAt a R z v).fderiv]
  simp [planeRadialCovector]
  ring

lemma corrugationDiskWell_center_second (a R : ℝ) (u v : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (corrugationDiskWell a R)) (0:ℝ × ℝ) u v =
      a*expNegInvGlue (R^2)*(u.1*v.1+u.2*v.2) := by
  simp [corrugationDiskWell_second]

lemma corrugationDiskWell_center_positive {a : ℝ} (ha : 0 ≤ a) (R : ℝ) (v : ℝ × ℝ) :
    0 ≤ fderiv ℝ (fderiv ℝ (corrugationDiskWell a R)) (0:ℝ × ℝ) v v := by
  rw [corrugationDiskWell_center_second]
  exact mul_nonneg (mul_nonneg ha (expNegInvGlue.nonneg _))
    (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))

end
end Yau.Geometry

end OAI
