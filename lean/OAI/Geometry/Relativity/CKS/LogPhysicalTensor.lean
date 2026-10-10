import OAI.Geometry.Relativity.CKS.LogPhysicalCoefficients

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def normalizeTensorLogFields (f : TensorFields) : TensorFields where
  base := normalizeMassLogFields f.base
  kr := fun y => radiusPower 5 y*f.kr y
  kb := fun y => radiusPower 3 y • f.kb y

def logRadialK (f : TensorFields) : Point → ℝ := fun y => 1/(1+Real.exp (y 0)^2)+f.kr y

def logOriginalL (f : TensorFields) : Point → ℝ := fun y =>
  (1/Real.sqrt (logSchur f.base y))^2*(logRadialK f y-
    2*∑ a, logShift f.base y a*f.kb y a+
    ∑ a, ∑ b, logTangentialK f.base y a b*(logShift f.base y a*logShift f.base y b))

def logOriginalEta (f : TensorFields) : Point → A → ℝ := fun y a =>
  (1/Real.sqrt (logSchur f.base y))*(f.kb y a-∑ b, logShift f.base y b*logTangentialK f.base y b a)

def logOriginalTau (f : TensorFields) : Point → Mat := fun y =>
  logTangentialK f.base y-
    (traceProduct (inverse (logGamma f.base y)) (logTangentialK f.base y)/2) • logGamma f.base y

lemma logTensorK_normalized (f : TensorFields) (y : Point) :
    tensorKField (radiusPower (-1)) (normalizeTensorLogFields f) y =
      (Real.exp (y 0)^2)⁻¹ • logTangentialK f.base y := by
  ext i k
  unfold tensorKField normalizeTensorLogFields normalizeMassLogFields logTangentialK
  simp only [radiusPower_inverse,radiusPower_two]
  dsimp
  have hr := Real.exp_ne_zero (y 0)
  field_simp

lemma logLapseSq_normalized {f : TensorFields} {y : Point} (hs : 0 < logSchur f.base y) :
    tensorLapseSqField (radiusPower (-1)) (normalizeTensorLogFields f) y =
      (1/Real.sqrt (logSchur f.base y))^2/Real.exp (y 0)^2 := by
  have hd := log_schur_coefficient f.base y
  unfold tensorLapseSqField tensorDenField
  change (1+radiusPower (-1) y^2)*(1+radiusPower (-1) y^3*
    cksVField (radiusPower (-1)) (normalizeMassLogFields f.base) y)⁻¹ = _
  rw [radiusPower_inverse,← hd]
  simp only [div_pow,one_pow,Real.sq_sqrt hs.le]
  have hr := Real.exp_ne_zero (y 0)
  have hrr : 1+Real.exp (y 0)^2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

lemma logLapse_normalized {f : TensorFields} {y : Point} (hs : 0 < logSchur f.base y) :
    tensorLapseField (radiusPower (-1)) (normalizeTensorLogFields f) y =
      (1/Real.sqrt (logSchur f.base y))/Real.exp (y 0) := by
  have hd := log_schur_coefficient f.base y
  have hden : 0 < tensorDenField (radiusPower (-1)) (normalizeTensorLogFields f) y := by
    unfold tensorDenField
    change 0 < 1+radiusPower (-1) y^3*cksVField (radiusPower (-1)) (normalizeMassLogFields f.base) y
    rw [radiusPower_inverse,← hd]
    positivity
  have ht := logLapseSq_normalized (f := f) hs
  have heq : (tensorLapseField (radiusPower (-1)) (normalizeTensorLogFields f) y)^2 =
      tensorLapseSqField (radiusPower (-1)) (normalizeTensorLogFields f) y := by
    unfold tensorLapseField tensorLapseSqField
    rw [mul_pow,Real.sq_sqrt (by positivity),inv_pow,Real.sq_sqrt hden.le]
  rw [ht,← div_pow] at heq
  have hleft : 0 ≤ tensorLapseField (radiusPower (-1)) (normalizeTensorLogFields f) y := by
    unfold tensorLapseField
    positivity
  have hright : 0 ≤ (1/Real.sqrt (logSchur f.base y))/Real.exp (y 0) := by positivity
  nlinarith [sq_nonneg (tensorLapseField (radiusPower (-1)) (normalizeTensorLogFields f) y-
    (1/Real.sqrt (logSchur f.base y))/Real.exp (y 0))]

lemma radiusPower_minus_three (y : Point) : radiusPower (-3) y = 1/Real.exp (y 0)^3 :=
  radiusPower_neg_nat 3 y

lemma logOriginalEta_normalized {f : TensorFields} {y : Point} (hs : 0 < logSchur f.base y) (a : A) :
    logOriginalEta f y a/Real.exp (y 0) =
      radiusPower (-3) y*tensorEtaField (radiusPower (-1)) (normalizeTensorLogFields f) y a := by
  unfold logOriginalEta tensorEtaField
  rw [logLapse_normalized hs,logTensorK_normalized]
  have hh := congrFun (logShift_normalized f.base) y
  have hh' (b : A) : cksHField (radiusPower (-1)) (normalizeMassLogFields f.base) y b =
      Real.exp (y 0)^5*logShift f.base y b := by
    have hb := congrFun hh b
    rw [radiusPower_minus_five] at hb
    dsimp at hb
    have hr := Real.exp_ne_zero (y 0)
    field_simp at hb ⊢
    nlinarith
  change _ = radiusPower (-3) y*((1/Real.sqrt (logSchur f.base y))/Real.exp (y 0)*
    (radiusPower 3 y*f.kb y a-∑ b, cksHField (radiusPower (-1)) (normalizeMassLogFields f.base) y b*
      ((Real.exp (y 0)^2)⁻¹*logTangentialK f.base y b a)))
  simp only [hh',radiusPower_minus_three,radiusPower_three]
  rw [show (∑ b, Real.exp (y 0)^5*logShift f.base y b*((Real.exp (y 0)^2)⁻¹*logTangentialK f.base y b a)) =
    Real.exp (y 0)^3*∑ b, logShift f.base y b*logTangentialK f.base y b a from by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      have hr := Real.exp_ne_zero (y 0)
      field_simp]
  have hr := Real.exp_ne_zero (y 0)
  field_simp

lemma logOriginalTau_normalized {f : TensorFields} {y : Point}
    (h0 : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f.base) y) ≠ 0) :
    (Real.exp (y 0)^2)⁻¹ • logOriginalTau f y = radiusPower (-3) y •
      tensorTauField (radiusPower (-1)) (normalizeTensorLogFields f) y := by
  have ht := log_trace_coefficient h0
  have ht' : traceProduct (inverse (logGamma f.base y)) (logTangentialK f.base y)/2 =
      1+(1/Real.exp (y 0))^3*cksTField (radiusPower (-1)) (normalizeMassLogFields f.base) y := by linarith [ht]
  unfold logOriginalTau tensorTauField
  rw [ht',logGamma_normalized,logTangentialK_normalized]
  ext i k
  change (Real.exp (y 0)^2)⁻¹*(Real.exp (y 0)^2*
    (cksQField (radiusPower (-1)) (normalizeMassLogFields f.base) y i k+
      (1/Real.exp (y 0))^3*(f.base.mK y i k-f.base.mg y i k+
        1/Real.exp (y 0)*(Real.exp (y 0)^2*f.base.ek y i k-Real.exp (y 0)^2*f.base.eg y i k)))-
    (1+(1/Real.exp (y 0))^3*cksTField (radiusPower (-1)) (normalizeMassLogFields f.base) y)*
      (radiusPower 2 y*cksQField (radiusPower (-1)) (normalizeMassLogFields f.base) y i k)) = _
  unfold normalizeTensorLogFields normalizeMassLogFields
  simp only [radiusPower_inverse,radiusPower_two,radiusPower_minus_three]
  dsimp
  have hr := Real.exp_ne_zero (y 0)
  field_simp
  ring

lemma logBB_normalized (f : TensorFields) (y : Point) :
    cksBBField (radiusPower (-1)) (normalizeMassLogFields f.base) y =
      Real.exp (y 0)^8*∑ a, ∑ b, inverse (logGamma f.base y) a b*(f.base.b y a*f.base.b y b) := by
  unfold cksBBField
  rw [logGamma_normalized]
  simp only [radiusPower_two,CKSAngularGeometry.inverse_smul _ _ (pow_ne_zero 2 (Real.exp_ne_zero (y 0))),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change inverse (cksQField (radiusPower (-1)) (normalizeMassLogFields f.base) y) a b*
    ((radiusPower 3 y*f.base.b y a)*(radiusPower 3 y*f.base.b y b)) = _
  rw [radiusPower_three]
  have hr := Real.exp_ne_zero (y 0)
  field_simp

lemma logShift_coefficient (f : TensorFields) (y : Point) (a : A) :
    cksHField (radiusPower (-1)) (normalizeMassLogFields f.base) y a =
      Real.exp (y 0)^5*logShift f.base y a := by
  have h := congrFun (congrFun (logShift_normalized f.base) y) a
  rw [radiusPower_minus_five] at h
  dsimp at h
  have hr := Real.exp_ne_zero (y 0)
  field_simp at h ⊢
  nlinarith

lemma logCross_normalized (f : TensorFields) (y : Point) :
    tensorCrossField (radiusPower (-1)) (normalizeTensorLogFields f) y =
      Real.exp (y 0)^8*∑ a, logShift f.base y a*f.kb y a := by
  unfold tensorCrossField
  change (∑ a, cksHField (radiusPower (-1)) (normalizeMassLogFields f.base) y a*
    (radiusPower 3 y*f.kb y a)) = _
  simp only [logShift_coefficient,radiusPower_three,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma logQuad_normalized (f : TensorFields) (y : Point) :
    tensorQuadField (radiusPower (-1)) (normalizeTensorLogFields f) y =
      Real.exp (y 0)^8*∑ a, ∑ b, logTangentialK f.base y a b*(logShift f.base y a*logShift f.base y b) := by
  unfold tensorQuadField
  rw [logTensorK_normalized]
  change (∑ a, ∑ b, ((Real.exp (y 0)^2)⁻¹*logTangentialK f.base y a b)*
    (cksHField (radiusPower (-1)) (normalizeMassLogFields f.base) y a*
      cksHField (radiusPower (-1)) (normalizeMassLogFields f.base) y b)) = _
  simp only [logShift_coefficient,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hr := Real.exp_ne_zero (y 0)
  field_simp

lemma logOriginalL_normalized {f : TensorFields} {y : Point} (hs : 0 < logSchur f.base y) :
    logOriginalL f y-1 = radiusPower (-3) y*
      tensorLField (radiusPower (-1)) (normalizeTensorLogFields f) y := by
  have hU : (1/Real.sqrt (logSchur f.base y))^2*logSchur f.base y = 1 := by
    rw [div_pow,one_pow,Real.sq_sqrt hs.le]
    field_simp
  unfold tensorLField
  erw [logLapseSq_normalized hs,logBB_normalized,logCross_normalized,logQuad_normalized]
  change logOriginalL f y-1 = radiusPower (-3) y*((1/Real.sqrt (logSchur f.base y))^2/Real.exp (y 0)^2*
    (radiusPower 5 y*f.kr y-f.base.mr y-radiusPower (-1) y*(radiusPower 6 y*f.base.err y)+
      radiusPower (-1) y^3*(Real.exp (y 0)^8*(∑ a, ∑ b, inverse (logGamma f.base y) a b*(f.base.b y a*f.base.b y b))-
        2*(Real.exp (y 0)^8*(∑ a, logShift f.base y a*f.kb y a))+
        Real.exp (y 0)^8*(∑ a, ∑ b, logTangentialK f.base y a b*(logShift f.base y a*logShift f.base y b)))))
  have h5 : radiusPower 5 y = Real.exp (y 0)^5 := radiusPower_nat 5 y
  rw [radiusPower_minus_three,radiusPower_inverse,h5,radiusPower_six]
  have hS : logSchur f.base y = logSchur f.base y := rfl
  change logSchur f.base y = logRadialMetric f.base y-
    ∑ a, ∑ b, inverse (logGamma f.base y) a b*(f.base.b y a*f.base.b y b) at hS
  unfold logRadialMetric at hS
  unfold logOriginalL logRadialK
  have hr := Real.exp_ne_zero (y 0)
  have hcoeff :
      (1/Real.exp (y 0)^3)*((1/Real.sqrt (logSchur f.base y))^2/Real.exp (y 0)^2*
      (Real.exp (y 0)^5*f.kr y-f.base.mr y-1/Real.exp (y 0)*(Real.exp (y 0)^6*f.base.err y)+
      (1/Real.exp (y 0))^3*(Real.exp (y 0)^8*(∑ a, ∑ b, inverse (logGamma f.base y) a b*(f.base.b y a*f.base.b y b))-
        2*(Real.exp (y 0)^8*(∑ a, logShift f.base y a*f.kb y a))+
        Real.exp (y 0)^8*(∑ a, ∑ b, logTangentialK f.base y a b*(logShift f.base y a*logShift f.base y b))))) =
      (1/Real.sqrt (logSchur f.base y))^2*(f.kr y-f.base.mr y/Real.exp (y 0)^5-f.base.err y+
        (∑ a, ∑ b, inverse (logGamma f.base y) a b*(f.base.b y a*f.base.b y b))-
        2*(∑ a, logShift f.base y a*f.kb y a)+
        (∑ a, ∑ b, logTangentialK f.base y a b*(logShift f.base y a*logShift f.base y b))) := by
    field_simp; ring
  rw [hcoeff]
  nlinarith [hU]

end
end CKSMixedGeometry

end

end OAI
