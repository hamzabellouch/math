import Mathlib
import OAI.Analysis.Conductivity.Fourier.TorusPoissonContinuous
import OAI.Analysis.Conductivity.Fourier.EndPoissonRepresentative

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

def endFrequency (s : Fin 3 → ℝ) (h : TorusModes) : (Fin 3 → ℝ) →L[ℝ] ℂ :=
  (-(torusRate s h:ℂ)) • Complex.ofRealCLM.comp (ContinuousLinearMap.proj 0) +
  (Complex.I*(h 0:ℂ)) • Complex.ofRealCLM.comp (ContinuousLinearMap.proj 1) +
  (Complex.I*(h 1:ℂ)) • Complex.ofRealCLM.comp (ContinuousLinearMap.proj 2)

lemma endFrequency_apply (s : Fin 3 → ℝ) (h : TorusModes) (x : Fin 3 → ℝ) :
    endFrequency s h x= (-(torusRate s h*x 0):ℝ)+
      (torusAngular h x:ℂ)*Complex.I := by
  simp [endFrequency,torusAngular]
  ring

lemma endFrequency_norm_le (s : Fin 3 → ℝ) (h : TorusModes) :
    ‖endFrequency s h‖≤torusRate s h+torusSize h := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by
    have hm : 0≤torusRate s h := Real.sqrt_nonneg _
    linarith [torusSize_nonneg h])
  intro v
  have hv (j : Fin 3) : ‖(v j:ℂ)‖≤‖v‖ := by simpa using norm_le_pi_norm v j
  have hm : 0≤torusRate s h := Real.sqrt_nonneg _
  change ‖-(torusRate s h:ℂ)*(v 0:ℂ)+Complex.I*(h 0:ℂ)*(v 1:ℂ)+
      Complex.I*(h 1:ℂ)*(v 2:ℂ)‖≤_
  calc
    _ ≤ ‖-(torusRate s h:ℂ)*(v 0:ℂ)‖+‖Complex.I*(h 0:ℂ)*(v 1:ℂ)‖+
        ‖Complex.I*(h 1:ℂ)*(v 2:ℂ)‖ := (norm_add_le _ _).trans
      (add_le_add (norm_add_le _ _) (le_refl _))
    _ = torusRate s h*‖(v 0:ℂ)‖+|(h 0:ℝ)| *‖(v 1:ℂ)‖+
        |(h 1:ℝ)| *‖(v 2:ℂ)‖ := by simp [abs_of_nonneg hm]
    _ ≤ torusRate s h*‖v‖+|(h 0:ℝ)| *‖v‖+|(h 1:ℝ)| *‖v‖ := by gcongr <;> exact hv _
    _ = _ := by dsimp [torusSize]; ring

def endFlatMode (s : Fin 3 → ℝ) (h : TorusModes) (a : ℂ) (x : Fin 3 → ℝ) : ℂ :=
  a*Complex.exp (endFrequency s h x)

lemma endFlatMode_eq (s : Fin 3 → ℝ) (h : TorusModes) (a : ℂ) (x : Fin 3 → ℝ) :
    endFlatMode s h a x=endPoissonModeField s h a 0 (x 0,torusAngles x) := by
  rw [endFlatMode,endFrequency_apply,Complex.exp_add,←Complex.ofReal_exp]
  rw [endPoissonModeField,mFourier_torusAngles]
  change a*((Real.exp (-(torusRate s h*x 0)):ℂ)*_) =
    (Real.exp (-torusRate s h*x 0):ℂ)*a*_
  rw [neg_mul]
  ring

lemma endFlatMode_norm (s : Fin 3 → ℝ) (h : TorusModes) (a : ℂ) (x : Fin 3 → ℝ) :
    ‖endFlatMode s h a x‖=‖a‖*Real.exp (-torusRate s h*x 0) := by
  rw [endFlatMode,norm_mul,Complex.norm_exp,endFrequency_apply]
  simp

lemma endFlatMode_hasFDeriv (s : Fin 3 → ℝ) (h : TorusModes) (a : ℂ) (x : Fin 3 → ℝ) :
    HasFDerivAt (endFlatMode s h a) (endFlatMode s h a x • endFrequency s h) x := by
  convert! ((endFrequency s h).hasFDerivAt (x:=x)).cexp.const_mul a using 1
  simp only [endFlatMode,mul_smul]

lemma endFlatMode_derivative_bound (s : Fin 3 → ℝ) (h : TorusModes)
    {a : ℂ} {B δ : ℝ} (ha : ‖a‖≤B) {x : Fin 3 → ℝ} (hx : δ≤x 0) :
    ‖endFlatMode s h a x • endFrequency s h‖≤
      B*((torusRate s h+torusSize h)*Real.exp (-δ*torusRate s h)) := by
  have hm : 0≤torusRate s h := Real.sqrt_nonneg _
  have hr : 0≤torusRate s h+torusSize h := add_nonneg hm (torusSize_nonneg h)
  have he : Real.exp (-torusRate s h*x 0)≤Real.exp (-δ*torusRate s h) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hx hm]
  rw [norm_smul,endFlatMode_norm]
  calc
    _ ≤ (B*Real.exp (-δ*torusRate s h))*(torusRate s h+torusSize h) :=
      mul_le_mul (mul_le_mul ha he (Real.exp_nonneg _) ((norm_nonneg _).trans ha))
        (endFrequency_norm_le s h) (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans ha) (Real.exp_nonneg _))
    _ = _ := by ring

def endFlatPoisson (s : Fin 3 → ℝ) (f : spectralTraceGraph (torusRate s))
    (x : Fin 3 → ℝ) : ℂ := ∑' h,endFlatMode s h (f.val 0 h) x

lemma endFlatPoisson_eq (s : Fin 3 → ℝ) (f : spectralTraceGraph (torusRate s))
    (x : Fin 3 → ℝ) :
    endFlatPoisson s f x=endPoissonField s f 0 (x 0,torusAngles x) := by
  exact tsum_congr (fun h => endFlatMode_eq s h (f.val 0 h) x)

lemma endFlatPoisson_derivative_summable (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) {x : Fin 3 → ℝ} (hx : 0<x 0) :
    Summable (fun h => endFlatMode s h (f.val 0 h) x • endFrequency s h) := by
  apply Summable.of_norm
  have hu : Summable (fun h => ‖f.val 0‖*((torusRate s h+torusSize h)*
      Real.exp (-x 0*torusRate s h))) := by
    simpa only [pow_one] using (flatMode_derivative_summable hs 1 hx).mul_left ‖f.val 0‖
  exact hu.of_nonneg_of_le (fun h => norm_nonneg _) (fun h =>
    endFlatMode_derivative_bound s h (lp.norm_apply_le_norm (by norm_num) (f.val 0) h) le_rfl)

theorem endFlatPoisson_hasFDeriv (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) {x : Fin 3 → ℝ} (hx : 0<x 0) :
    HasFDerivAt (endFlatPoisson s f)
      (∑' h,endFlatMode s h (f.val 0 h) x • endFrequency s h) x := by
  have hu : Summable (fun h => ‖f.val 0‖*((torusRate s h+torusSize h)*
      Real.exp (-(x 0/2)*torusRate s h))) := by
    simpa only [pow_one] using
      (flatMode_derivative_summable hs 1 (show 0<x 0/2 by linarith)).mul_left ‖f.val 0‖
  exact hasFDerivAt_tsum_of_isPreconnected hu (axial_halfspace_open (x 0/2))
    (axial_halfspace_connected (x 0/2))
    (fun h y _ => endFlatMode_hasFDeriv s h (f.val 0 h) y)
    (fun h y hy => endFlatMode_derivative_bound s h
      (lp.norm_apply_le_norm (by norm_num) (f.val 0) h) hy.le)
    (show x 0/2<x 0 by linarith)
    (by simpa only [endFlatMode_eq] using (endPoissonField_hasSum s hs f 0 (z:=(x 0,torusAngles x)) hx).summable)
    (show x 0/2<x 0 by linarith)

lemma endFlatMode_axis (s : Fin 3 → ℝ) (h : TorusModes) (a : ℂ)
    (x : Fin 3 → ℝ) (j : Fin 3) :
    (endFlatMode s h a x • endFrequency s h) (Pi.single j 1)=
      endPoissonModeField s h a j.succ (x 0,torusAngles x) := by
  rw [smul_apply,smul_eq_mul,endFlatMode_eq]
  fin_cases j <;> simp [endFrequency,endPoissonModeField,endModeCoefficient] <;> ring

lemma endFlatPoisson_derivative_axis (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) {x : Fin 3 → ℝ} (hx : 0<x 0) (j : Fin 3) :
    fderiv ℝ (endFlatPoisson s f) x (Pi.single j 1)=
      endPoissonField s f j.succ (x 0,torusAngles x) := by
  calc
    _ = (∑' h,endFlatMode s h (f.val 0 h) x • endFrequency s h) (Pi.single j 1) :=
      congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℂ => L (Pi.single j 1))
        (endFlatPoisson_hasFDeriv s hs f hx).fderiv
    _ = ∑' h,(endFlatMode s h (f.val 0 h) x • endFrequency s h) (Pi.single j 1) :=
      (ContinuousLinearMap.apply ℝ ℂ (Pi.single j 1)).map_tsum
        (endFlatPoisson_derivative_summable s hs f hx)
    _ = _ := tsum_congr (fun h => endFlatMode_axis s h (f.val 0 h) x j)

lemma endFlatPoisson_real_derivative_axis (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) {x : Fin 3 → ℝ} (hx : 0<x 0) (j : Fin 3) :
    fderiv ℝ (fun y => (endFlatPoisson s f y).re) x (Pi.single j 1)=
      (endPoissonField s f j.succ (x 0,torusAngles x)).re := by
  have he := endFlatPoisson_hasFDeriv s hs f hx
  have hr := (Complex.reCLM.hasFDerivAt.comp x he).fderiv
  calc
    _ = ((∑' h,endFlatMode s h (f.val 0 h) x • endFrequency s h) (Pi.single j 1)).re :=
      congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℝ => L (Pi.single j 1)) hr
    _ = (fderiv ℝ (endFlatPoisson s f) x (Pi.single j 1)).re :=
      congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℂ => (L (Pi.single j 1)).re) he.fderiv.symm
    _ = _ := congrArg Complex.re (endFlatPoisson_derivative_axis s hs f hx j)

end ScalarConductivity

end

end OAI
