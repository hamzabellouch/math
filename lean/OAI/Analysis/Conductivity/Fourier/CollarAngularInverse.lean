import Mathlib
import OAI.Analysis.Conductivity.Sources.AngularTrace

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

def complexUnitAngle (z : ℂ) : UnitAddCircle := (z.arg/(2*Real.pi) : ℝ)

lemma measurable_complexUnitAngle : Measurable complexUnitAngle := by
  exact (show Continuous (fun x : ℝ => (x : UnitAddCircle)) from continuous_quotient_mk').measurable.comp
    (Complex.measurable_arg.div_const _)

lemma fourier_complexUnitAngle (z : ℂ) :
    fourier 1 (complexUnitAngle z)=Complex.exp ((z.arg : ℂ)*Complex.I) := by
  rw [complexUnitAngle,fourier_coe_apply]
  congr 1
  push_cast
  field_simp

lemma complexUnitAngle_fourier (x : UnitAddCircle) :
    complexUnitAngle (fourier 1 x)=x := by
  apply AddCircle.injective_toCircle (by norm_num : (1:ℝ)≠0)
  apply Subtype.ext
  have hn : ‖fourier 1 x‖=1 := by simp [fourier_apply,Circle.norm_coe]
  have he := Complex.norm_mul_exp_arg_mul_I (fourier 1 x)
  rw [hn,Complex.ofReal_one,one_mul,←fourier_complexUnitAngle] at he
  simpa [fourier_apply] using he

lemma complexUnitAngle_pos_mul (z : ℂ) {r : ℝ} (hr : 0<r) :
    complexUnitAngle ((r:ℂ)*z)=complexUnitAngle z := by
  simp only [complexUnitAngle,Complex.arg_real_mul z hr]

lemma rectangularRay_max {w : ℝ} (hw : 0<w) (hw' : w≤1) (θ : UnitAddCircle) :
    max (|rectangularRay w θ 0|/w) |rectangularRay w θ 1|=1 := by
  have hd : 0<rayDenominator w θ := lt_of_lt_of_le (by norm_num) (rayDenominator_lower hw hw' θ)
  simp only [rectangularRay,abs_div,abs_of_pos hd]
  rw [div_right_comm _ _ w,max_div_div_right hd.le]
  exact div_self hd.ne'

lemma rectangularRay_first_abs {w : ℝ} (hw : 0<w) (hw' : w≤1) (θ : UnitAddCircle) :
    |rectangularRay w θ 0|≤w := by
  have hh := (le_max_left _ _).trans (rectangularRay_max hw hw' θ).le
  exact (div_le_iff₀ hw).mp hh |>.trans_eq (one_mul w)

lemma sourceAngular_radius_pos {t : ℝ} (ht : t∈Icc (-(1:ℝ)/100) (1/100))
    (θ : UnitAddTorus (Fin 2)) :
    0<sourceRadialCenter+(1-t)*rectangularRay sourceRadialWidth (θ 1) 0 := by
  have hh := abs_le.mp (rectangularRay_first_abs (w:=sourceRadialWidth)
    (by norm_num [sourceRadialWidth,sourceHole]) (by norm_num [sourceRadialWidth,sourceHole]) (θ 1))
  have ht' : 0≤1-t := by linarith [ht.2]
  have hm := mul_le_mul_of_nonneg_left hh.1 ht'
  norm_num [sourceRadialWidth,sourceRadialCenter,sourceHole] at *
  linarith

lemma sourceAngular_radial {t : ℝ} (ht : t∈Icc (-(1:ℝ)/100) (1/100))
    (θ : UnitAddTorus (Fin 2)) :
    sourceRadial (sourceAngularCollar t θ)=
      sourceRadialCenter+(1-t)*rectangularRay sourceRadialWidth (θ 1) 0 := by
  have hr := sourceAngular_radius_pos ht θ
  have hL : 0<sourceLength := by norm_num [sourceLength]
  let R := sourceRadialCenter+(1-t)*rectangularRay sourceRadialWidth (θ 1) 0
  change 0<R at hr
  change max (|sourceLength*R*rectangularRay 1 (θ 0) 0|/sourceLength)
    |R*rectangularRay 1 (θ 0) 1|=R
  simp only [abs_mul,abs_of_pos hL,abs_of_pos hr]
  rw [mul_assoc,mul_div_cancel_left₀ _ hL.ne',←mul_max_of_nonneg _ _ hr.le]
  have hh := rectangularRay_max (w:=1) (by norm_num) (by norm_num) (θ 0)
  simpa only [div_one,mul_one] using congrArg
    (fun z => (sourceRadialCenter+(1-t)*rectangularRay sourceRadialWidth (θ 1) 0)*z) hh

lemma sourceAngular_time {t : ℝ} (ht : t∈Icc (-(1:ℝ)/100) (1/100))
    (θ : UnitAddTorus (Fin 2)) : sourceCollarTime (sourceAngularCollar t θ)=t := by
  have hs : 0<1-t := by linarith [ht.2]
  have hw : 0<sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  rw [sourceCollarTime]
  simp only [sourceCrossCoordinates,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [sourceAngular_radial ht,add_sub_cancel_left,mul_div_assoc,abs_mul,abs_of_pos hs]
  change 1-max ((1-t)*|(rectangularRay sourceRadialWidth (θ 1) 0)/sourceRadialWidth|)
    |(1-t)*rectangularRay sourceRadialWidth (θ 1) 1|=t
  rw [abs_div,abs_of_pos hw,abs_mul,abs_of_pos hs,←mul_max_of_nonneg _ _ hs.le,
    rectangularRay_max hw (by norm_num [sourceRadialWidth,sourceHole]) (θ 1), mul_one]
  ring

def sourceComplexDirections (y : Fin 3 → ℝ) : Fin 2 → ℂ :=
  ![((y 0/sourceLength:ℝ):ℂ)+Complex.I*(y 1:ℂ),
    ((sourceRadial y-sourceRadialCenter:ℝ):ℂ)+Complex.I*(y 2:ℂ)]

def sourcePhysicalAngles (y : Fin 3 → ℝ) : UnitAddTorus (Fin 2) :=
  fun i => complexUnitAngle (sourceComplexDirections y i)

lemma continuous_sourceComplexDirections : Continuous sourceComplexDirections := by
  apply continuous_pi
  intro i
  fin_cases i <;> unfold sourceComplexDirections sourceRadial <;> fun_prop

lemma measurable_sourcePhysicalAngles : Measurable sourcePhysicalAngles := by
  apply Measurable.of_eval
  intro i
  exact measurable_complexUnitAngle.comp
    (((continuous_apply i).comp continuous_sourceComplexDirections).measurable)

lemma sourceComplexDirections_angular {t : ℝ} (ht : t∈Icc (-(1:ℝ)/100) (1/100))
    (θ : UnitAddTorus (Fin 2)) :
    sourceComplexDirections (sourceAngularCollar t θ)=
      ![(((sourceRadialCenter+(1-t)*rectangularRay sourceRadialWidth (θ 1) 0)/
          rayDenominator 1 (θ 0):ℝ):ℂ)*fourier 1 (θ 0),
        (((1-t)/rayDenominator sourceRadialWidth (θ 1):ℝ):ℂ)*fourier 1 (θ 1)] := by
  ext i
  fin_cases i
  · apply Complex.ext <;>
      simp [sourceComplexDirections,sourceAngularCollar,sourceAngularPolynomial,
        sourceRayCoordinates,rectangularRay,rayDirection,Complex.mul_re,Complex.mul_im] <;>
      norm_num [sourceLength] <;> ring
  · change ((sourceRadial (sourceAngularCollar t θ)-sourceRadialCenter:ℝ):ℂ)+
      Complex.I*((sourceAngularCollar t θ) 2:ℂ)=_
    rw [sourceAngular_radial ht,add_sub_cancel_left]
    apply Complex.ext <;>
      simp [sourceAngularCollar,sourceAngularPolynomial,sourceRayCoordinates,
        rectangularRay,rayDirection,Complex.mul_re,Complex.mul_im] <;> ring

lemma sourcePhysicalAngles_angular {t : ℝ} (ht : t∈Icc (-(1:ℝ)/100) (1/100))
    (θ : UnitAddTorus (Fin 2)) : sourcePhysicalAngles (sourceAngularCollar t θ)=θ := by
  have h0 : 0<rayDenominator 1 (θ 0) :=
    lt_of_lt_of_le (by norm_num) (rayDenominator_lower (by norm_num) (by norm_num) _)
  have h1 : 0<rayDenominator sourceRadialWidth (θ 1) :=
    lt_of_lt_of_le (by norm_num) (rayDenominator_lower
      (by norm_num [sourceRadialWidth,sourceHole]) (by norm_num [sourceRadialWidth,sourceHole]) _)
  ext i
  change complexUnitAngle (sourceComplexDirections (sourceAngularCollar t θ) i)=θ i
  rw [sourceComplexDirections_angular ht]
  fin_cases i
  · exact (complexUnitAngle_pos_mul _ (div_pos (sourceAngular_radius_pos ht θ) h0)).trans
      (complexUnitAngle_fourier _)
  · exact (complexUnitAngle_pos_mul _ (div_pos (by linarith [ht.2] : 0<1-t) h1)).trans
      (complexUnitAngle_fourier _)

end ScalarConductivity

end

end OAI
