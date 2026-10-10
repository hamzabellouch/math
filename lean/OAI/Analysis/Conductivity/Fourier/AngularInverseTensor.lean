import Mathlib
import OAI.Analysis.Conductivity.Fourier.GeneralModeFiniteEndNormal

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma angularLiftMatrix_background {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (s : Fin 3 → ℝ) :
    angularLiftMatrix A*flatBackgroundTensor (normalizedAngularTensor s A)*(angularLiftMatrix A)ᵀ=
      angularNormalization A • flatBackgroundTensor s := by
  have hd := congrArg (fun z : ℝ => z^2) (real_angular_det_one hA)
  norm_num only [one_pow] at hd
  have hm := Real.sq_sqrt (angularNormalization_pos A).le
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_three,Matrix.transpose_apply,
      angularLiftMatrix,flatBackgroundTensor,normalizedAngularTensor]
  · nlinarith [hm]
  · linear_combination angularNormalization A * s 0 * hd
  · linear_combination angularNormalization A * s 1 * hd
  · linear_combination angularNormalization A * s 1 * hd
  · linear_combination angularNormalization A * s 2 * hd

lemma angularInverseLift_shift (A : Matrix (Fin 2) (Fin 2) ℤ)
    (T : ℝ) (n : Fin 2 → ℤ) (x : Coord3) :
    angularInverseLift A (x+angularShift T n)=angularInverseLift A x+
      angularShift T ![A 1 1*n 0-A 0 1*n 1,-A 1 0*n 0+A 0 0*n 1] := by
  ext i
  fin_cases i <;> simp [angularInverseLift,angularShift] <;> ring

lemma AngularPeriodic.angularInverseLift {E : Type*} {T : ℝ} {f : Coord3 → E}
    (hf : AngularPeriodic T f) (A : Matrix (Fin 2) (Fin 2) ℤ) :
    AngularPeriodic T (f ∘ angularInverseLift A) := by
  intro n x
  simp only [Function.comp_apply,angularInverseLift_shift]
  exact hf _ _

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix Real
open scoped Matrix.Norms.Elementwise

def undoAngularPoint (A : Matrix (Fin 2) (Fin 2) ℤ) (θ : Fin 2 → ℝ)
    (d : ℝ) (x : Coord3) : Coord3 :=
  angularInverseLift A (x-![d,0,0])-![0,θ 0,θ 1]

lemma undoAngularPoint_zero (A : Matrix (Fin 2) (Fin 2) ℤ) (θ : Fin 2 → ℝ)
    (d : ℝ) (x : Coord3) :
    undoAngularPoint A θ d x 0=(x 0-d)/sqrt (angularNormalization A) := by
  simp [undoAngularPoint,angularInverseLift]

lemma undoAngularPoint_forward {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (θ : Fin 2 → ℝ) (d : ℝ) (x : Coord3) :
    angularNormalizedLift A (angularRealTranslation θ (undoAngularPoint A θ d x))=x-![d,0,0] := by
  have he : angularRealTranslation θ (undoAngularPoint A θ d x)=
      angularInverseLift A (x-![d,0,0]) := by
    ext i
    fin_cases i <;> simp [angularRealTranslation,undoAngularPoint]
  rw [he,angularNormalizedLift_inverse hA]

lemma undoAngularPoint_contDiff {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det=1)
    (θ : Fin 2 → ℝ) (d : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (undoAngularPoint A θ d) :=
  (((angularNormalizedEquiv A hA).symm.contDiff).comp
    (contDiff_id.sub contDiff_const)).sub contDiff_const

lemma AngularPeriodic.undoAngularPoint {F : Type*} {T : ℝ} {f : Coord3 → F}
    (hf : AngularPeriodic T f) (A : Matrix (Fin 2) (Fin 2) ℤ) (θ : Fin 2 → ℝ) (d : ℝ) :
    AngularPeriodic T (f ∘ undoAngularPoint A θ d) := by
  intro n x
  simp only [Function.comp_apply,ScalarConductivity.undoAngularPoint]
  rw [show x+angularShift T n-![d,0,0]=(x-![d,0,0])+angularShift T n by abel,
    angularInverseLift_shift]
  rw [show ScalarConductivity.angularInverseLift A (x-![d,0,0])+
    angularShift T ![A 1 1*n 0-A 0 1*n 1,-A 1 0*n 0+A 0 0*n 1]-![0,θ 0,θ 1]=
    (ScalarConductivity.angularInverseLift A (x-![d,0,0])-![0,θ 0,θ 1])+
    angularShift T ![A 1 1*n 0-A 0 1*n 1,-A 1 0*n 0+A 0 0*n 1] by abel]
  exact hf _ _

def undoAngularValue (A : Matrix (Fin 2) (Fin 2) ℤ) (θ : Fin 2 → ℝ)
    (d lam : ℝ) (v : Coord3 → Fin 2 → ℝ) (x : Coord3) : Fin 2 → ℝ :=
  ![sqrt (angularNormalization A)*v (undoAngularPoint A θ d x) 0+d,
    exp (-lam*d)*v (undoAngularPoint A θ d x) 1]

def undoAngularTensor (A : Matrix (Fin 2) (Fin 2) ℤ) (θ : Fin 2 → ℝ)
    (d : ℝ) (E : Coord3 → Mat3) (x : Coord3) : Mat3 :=
  (angularNormalization A)⁻¹ •
    (angularLiftMatrix A*E (undoAngularPoint A θ d x)*(angularLiftMatrix A)ᵀ)

lemma undoAngularValue_matching {s : Fin 3 → ℝ} {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : A.det=1) (θ : Fin 2 → ℝ) (d : ℝ) (h₀ : Fin 2 → ℤ)
    (a b pa pb : (Fin 2 → ℤ) → ℝ) {v : Coord3 → Fin 2 → ℝ}
    (hv : ∀ y,y 0∈Icc 0 (1/2) → v y=
      ![y 0+flatFourier s (normalizedFourierCoefficients s 0 d a) pa
        (angularNormalizedLift A (angularRealTranslation θ y))/sqrt (angularNormalization A),
        flatPhaseMode s h₀ (pb h₀) (angularNormalizedLift A (angularRealTranslation θ y))+
        flatFourier s (normalizedFourierCoefficients s (torusRate s h₀) d b) pb
          (angularNormalizedLift A (angularRealTranslation θ y))])
    {x : Coord3} (hx : (x 0-d)/sqrt (angularNormalization A)∈Icc 0 (1/2)) :
    undoAngularValue A θ d (torusRate s h₀) v x=
      ![x 0+flatFourier s a pa x,flatPhaseMode s h₀ (pb h₀) x+flatFourier s b pb x] := by
  have hm : sqrt (angularNormalization A)≠0 := (sqrt_pos.mpr (angularNormalization_pos A)).ne'
  have hxy : (x-![d,0,0])+![d,0,0]=x := sub_add_cancel _ _
  have he : exp (-torusRate s h₀*d)*exp (torusRate s h₀*d)=1 := by
    rw [←exp_add,show -torusRate s h₀*d+torusRate s h₀*d=0 by ring,exp_zero]
  have hmode := flatPhaseMode_translation s h₀ (pb h₀) d (x-![d,0,0])
  rw [hxy] at hmode
  unfold undoAngularValue
  rw [hv _ (by simpa only [undoAngularPoint_zero] using hx),undoAngularPoint_forward hA,
    flatFourier_normalized_translation,flatFourier_normalized_translation,hxy]
  ext j
  fin_cases j
  · change sqrt (angularNormalization A)*(undoAngularPoint A θ d x 0+
      exp (0*d)*flatFourier s a pa x/sqrt (angularNormalization A))+d=x 0+flatFourier s a pa x
    rw [undoAngularPoint_zero]
    simp only [zero_mul,exp_zero,one_mul]
    field_simp [hm]
    ring
  · change exp (-torusRate s h₀*d)*(flatPhaseMode s h₀ (pb h₀) (x-![d,0,0])+
      exp (torusRate s h₀*d)*flatFourier s b pb x)=_
    rw [mul_add,←mul_assoc,he,one_mul,←hmode]
    rfl

lemma undoAngularTensor_matching {s : Fin 3 → ℝ} {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : A.det=1) (θ : Fin 2 → ℝ) (d : ℝ) {E : Coord3 → Mat3}
    (hE : ∀ y,y 0∈Icc 0 (1/2) → E y=flatBackgroundTensor (normalizedAngularTensor s A))
    {x : Coord3} (hx : (x 0-d)/sqrt (angularNormalization A)∈Icc 0 (1/2)) :
    undoAngularTensor A θ d E x=flatBackgroundTensor s := by
  rw [undoAngularTensor,hE _ (by simpa only [undoAngularPoint_zero] using hx),
    angularLiftMatrix_background hA,smul_smul,inv_mul_cancel₀ (angularNormalization_pos A).ne',one_smul]

lemma undoAngularValue_terminal (A : Matrix (Fin 2) (Fin 2) ℤ) (θ : Fin 2 → ℝ)
    (d lam T : ℝ) {v : Coord3 → Fin 2 → ℝ} (hv : ∀ y,T≤y 0 → v y=![y 0,0])
    {x : Coord3} (hx : d+sqrt (angularNormalization A)*T≤x 0) :
    undoAngularValue A θ d lam v x=![x 0,0] := by
  have hm : 0<sqrt (angularNormalization A) := sqrt_pos.mpr (angularNormalization_pos A)
  have hy : T≤undoAngularPoint A θ d x 0 := by
    rw [undoAngularPoint_zero,le_div_iff₀ hm]
    nlinarith
  unfold undoAngularValue
  rw [hv _ hy]
  ext j
  fin_cases j
  · change sqrt (angularNormalization A)*undoAngularPoint A θ d x 0+d=x 0
    rw [undoAngularPoint_zero]
    field_simp [hm.ne']
    ring
  · simp

end ScalarConductivity

end
end

end OAI
