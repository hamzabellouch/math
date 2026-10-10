import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.CubeGradient
import OAI.Analysis.CoulombRadii.Localization.RegularizedBounds

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace Coulomb
lemma oneBody_derivative {n:ℕ} (f:Space → ℝ) (hf:ContDiff ℝ ∞ f)
    (i j:Fin n) (b:Fin 3) (x:Configuration n) :
    fderiv ℝ (fun y => f (position y i)) x (EuclideanSpace.single (j,b) 1)=
      if i=j then fderiv ℝ f (position x i) (EuclideanSpace.single b 1) else 0 := by
  have H:=(((hf.differentiable (by simp) (position x i)).hasFDerivAt).comp x
    (positionCLM i).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => f (position y i)) x=_ at H
  rw [H]
  simp only [ContinuousLinearMap.comp_apply,positionCLM_single]
  split_ifs <;> simp_all
lemma oneBody_second_derivative {n:ℕ} (f:Space → ℝ) (hf:ContDiff ℝ ∞ f)
    (i j k:Fin n) (a b:Fin 3) (x:Configuration n) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => f (position z i)) y (EuclideanSpace.single (j,a) 1))
      x (EuclideanSpace.single (k,b) 1)=
      if i=j ∧ i=k then fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single a 1))
        (position x i) (EuclideanSpace.single b 1) else 0 := by
  have hd:ContDiff ℝ ∞ (fun y => fderiv ℝ f y (EuclideanSpace.single a 1)):=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  simp_rw [oneBody_derivative f hf]
  by_cases hj:i=j
  · simp only [hj,ite_true,true_and]
    exact oneBody_derivative _ hd j k b x
  · simp [hj]
structure SmoothBoundedCoefficient where
  value:Space → ℝ
  smooth:ContDiff ℝ ∞ value
  bound:ℝ
  derivBound:ℝ
  bound_nonneg:0≤bound
  derivBound_nonneg:0≤derivBound
  value_le:∀ x,|value x|≤bound
  deriv_le:∀ a x,|fderiv ℝ value x (EuclideanSpace.single a 1)|≤derivBound
namespace SmoothBoundedCoefficient
lemma lift_smooth (f:SmoothBoundedCoefficient) {n:ℕ} (i:Fin n) :
    ContDiff ℝ ∞ (fun x:Configuration n => f.value (position x i)) :=
  f.smooth.comp (positionCLM i).contDiff
lemma lift_deriv_le (f:SmoothBoundedCoefficient) {n:ℕ} (i:Fin n) (a:Fin n × Fin 3) (x:Configuration n) :
    |fderiv ℝ (fun y => f.value (position y i)) x (EuclideanSpace.single a 1)|≤f.derivBound := by
  rw [oneBody_derivative f.value f.smooth i a.1 a.2 x]
  split_ifs
  · exact f.deriv_le _ _
  · simpa using f.derivBound_nonneg
end SmoothBoundedCoefficient

def regularizedU (l e:ℝ) (x:Space):ℝ:=NeutralAtom.regularizedKernel l x+e
lemma regularizedU_pos {l e:ℝ} (he:0<e) (x:Space):0<regularizedU l e x :=
  add_pos_of_nonneg_of_pos (Real.rpow_nonneg (by positivity) _) he
lemma regularizedU_ge {l e:ℝ} (x:Space):e≤regularizedU l e x := by
  unfold regularizedU NeutralAtom.regularizedKernel
  have H:=Real.rpow_nonneg (by positivity : 0≤‖x‖^2+l^2) (-1/2:ℝ)
  linarith
lemma regularizedU_partial {l:ℝ} (hl:l≠0) (e:ℝ) (a:Fin 3) (x:Space):
    fderiv ℝ (regularizedU l e) x (EuclideanSpace.single a 1)=
      NeutralAtom.dirPartial (NeutralAtom.regularizedKernel l) (NeutralAtom.axis a) x := by
  unfold regularizedU NeutralAtom.dirPartial NeutralAtom.axis
  have hderiv := ((NeutralAtom.contDiff_regularizedKernel hl).differentiable (by simp) x).hasFDerivAt
  rw [(hderiv.add_const e).fderiv]
lemma regularizedU_smooth {l:ℝ} (hl:l≠0) (e:ℝ):ContDiff ℝ ∞ (regularizedU l e):=
  (NeutralAtom.contDiff_regularizedKernel hl).add contDiff_const

def reciprocalCoefficient (l e:ℝ) (hl:l≠0) (he:0<e):SmoothBoundedCoefficient where
  value x := (regularizedU l e x)⁻¹
  smooth := (regularizedU_smooth hl e).inv (fun x => (regularizedU_pos he x).ne')
  bound := e⁻¹
  derivBound := ((l^2)^(-1/2:ℝ)+(l^2)^(-3/2:ℝ))/e^2
  bound_nonneg := le_of_lt (inv_pos.mpr he)
  derivBound_nonneg := by positivity
  value_le x := by
    rw [abs_of_pos (inv_pos.mpr (regularizedU_pos he x))]
    exact inv_anti₀ he (regularizedU_ge x)
  deriv_le a x := by
    have H:=((hasDerivAt_inv (regularizedU_pos he x).ne').comp_hasFDerivAt x
      (((regularizedU_smooth hl e).differentiable (by simp) x).hasFDerivAt)).fderiv
    change fderiv ℝ (fun y => (regularizedU l e y)⁻¹) x=_ at H
    rw [H]
    simp only [smul_apply,smul_eq_mul,abs_mul,abs_neg,
      abs_inv,abs_of_nonneg (sq_nonneg (regularizedU l e x))]
    rw [regularizedU_partial hl]
    have hd:=NeutralAtom.regularizedPartial_uniform_bound hl x a
    have hu:(e^2)≤(regularizedU l e x)^2:=sq_le_sq₀ he.le (regularizedU_pos he x).le |>.mpr (regularizedU_ge x)
    have hh:=mul_le_mul (inv_anti₀ (sq_pos_of_pos he) hu) hd (abs_nonneg _) (by positivity)
    simpa only [div_eq_mul_inv,mul_comm] using hh

def rootReciprocalCoefficient (l e:ℝ) (hl:l≠0) (he:0<e):SmoothBoundedCoefficient where
  value x := (regularizedU l e x)^(-1/2:ℝ)
  smooth := (regularizedU_smooth hl e).rpow_const_of_ne (fun x => (regularizedU_pos he x).ne')
  bound := e^(-1/2:ℝ)
  derivBound := (1/2:ℝ)*e^(-3/2:ℝ)*((l^2)^(-1/2:ℝ)+(l^2)^(-3/2:ℝ))
  bound_nonneg := Real.rpow_nonneg he.le _
  derivBound_nonneg := by positivity
  value_le x := by
    rw [abs_of_nonneg (Real.rpow_nonneg (regularizedU_pos he x).le _)]
    exact Real.rpow_le_rpow_of_nonpos he (regularizedU_ge x) (by norm_num)
  deriv_le a x := by
    have H:=((((regularizedU_smooth hl e).differentiable (by simp) x).hasFDerivAt).rpow_const
      (p:=(-1/2:ℝ)) (Or.inl (regularizedU_pos he x).ne')).fderiv
    rw [H]
    simp only [smul_apply,smul_eq_mul,abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (regularizedU_pos he x).le _),regularizedU_partial hl]
    rw [show (-1/2:ℝ)-1=(-3/2:ℝ) by norm_num,show |(-1/2:ℝ)|=(1/2:ℝ) by norm_num]
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos he (regularizedU_ge x) (by norm_num)) (by norm_num)
    · exact NeutralAtom.regularizedPartial_uniform_bound hl x a
    · exact abs_nonneg _
    · positivity
lemma rootReciprocalCoefficient_sq (l e:ℝ) (hl:l≠0) (he:0<e) (x:Space):
    ((rootReciprocalCoefficient l e hl he).value x)^2=(reciprocalCoefficient l e hl he).value x := by
  change ((regularizedU l e x)^(-1/2:ℝ))^2=(regularizedU l e x)⁻¹
  rw [←Real.rpow_two,←Real.rpow_mul (regularizedU_pos he x).le]
  norm_num [Real.rpow_neg_one]

end Coulomb
end

end

end OAI
