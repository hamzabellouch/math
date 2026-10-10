import OAI.Geometry.Relativity.CKS.CKSFoliationFields
import OAI.Geometry.Relativity.CKS.LogPhysicalMass
import OAI.Geometry.Relativity.CKS.LogPhysicalTensor

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def logLapse (f : MassFields) : Point → ℝ := fun y => 1/Real.sqrt (logSchur f y)
def logU (f : MassFields) : Point → ℝ := fun y => logLapse f y*logExpansion f y
def logT (f : MassFields) : Point → ℝ := fun y =>
  (1/2:ℝ)*traceProduct (CKSAngularGeometry.inverse (logGamma f y)) (logTangentialK f y)

lemma foliationDenField_positive {f : MassFields} {x : Point} (h : 0 < logSchur f x) :
    0 < foliationDenField (radiusPower (-1)) (normalizeMassLogFields f) x := by
  change 0 < 1+radiusPower (-1) x^3*cksVField (radiusPower (-1)) (normalizeMassLogFields f) x
  rw [radiusPower_inverse,← log_schur_coefficient]
  positivity
lemma log_lapse_normalized {f : MassFields} {x : Point} (h : 0 < logSchur f x) :
    logLapse f x/Real.sqrt (1+Real.exp (x 0)^2)-1 =
      radiusPower (-3) x*lapseCorrectionField (radiusPower (-1)) (normalizeMassLogFields f) x := by
  have hden := foliationDenField_positive h
  have heq : logLapse f x/Real.sqrt (1+Real.exp (x 0)^2) =
      (Real.sqrt (foliationDenField (radiusPower (-1)) (normalizeMassLogFields f) x))⁻¹ := by
    unfold logLapse foliationDenField
    rw [radiusPower_inverse,← log_schur_coefficient,Real.sqrt_mul (by positivity)]
    simp only [div_eq_mul_inv]
    ring
  rw [heq]
  have hz3 : radiusPower (-1) x^3 = radiusPower (-3) x := by
    rw [radiusPower_inverse,radiusPower_minus_three]
    ring
  have hh := reciprocal_sqrt_factor (z := radiusPower (-1) x)
    (V := cksVField (radiusPower (-1)) (normalizeMassLogFields f) x) hden
  simpa only [foliationDenField,lapseCorrectionField,hz3] using hh
lemma log_u_normalized {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) ≠ 0)
    (h : 0 < logSchur f x) :
    logU f x/Real.sqrt (1+Real.exp (x 0)^2)-1 =
      radiusPower (-3) x*uCorrectionField (radiusPower (-1)) (normalizeMassLogFields f) x := by
  have hl := log_lapse_normalized h
  have hd := log_expansion_coefficient hf h0
  have hz3 : (1/Real.exp (x 0))^3 = radiusPower (-3) x := by rw [radiusPower_minus_three]; ring
  rw [hz3] at hd
  unfold logU uCorrectionField
  rw [hd]
  rw [radiusPower_inverse,hz3]
  rw [mul_div_right_comm,show logLapse f x/Real.sqrt (1+Real.exp (x 0)^2) =
    1+radiusPower (-3) x*lapseCorrectionField (radiusPower (-1)) (normalizeMassLogFields f) x by linarith]
  ring

end
end CKSMixedGeometry

end

end OAI
