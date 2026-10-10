import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

def rayDirection (θ : UnitAddCircle) : Fin 2 → ℝ :=
  ![(fourier 1 θ).re,(fourier 1 θ).im]

def rayDenominator (w : ℝ) (θ : UnitAddCircle) : ℝ :=
  max (|rayDirection θ 0|/w) |rayDirection θ 1|

def rectangularRay (w : ℝ) (θ : UnitAddCircle) : Fin 2 → ℝ :=
  fun i => rayDirection θ i/rayDenominator w θ

lemma rayDirection_unit (θ : UnitAddCircle) :
    (rayDirection θ 0)^2+(rayDirection θ 1)^2=1 := by
  have hh : ‖fourier 1 θ‖=1 := by simp [fourier_apply,Circle.norm_coe]
  have hs := Complex.sq_norm (fourier 1 θ)
  rw [hh,Complex.normSq_apply] at hs
  simpa [rayDirection,pow_two] using hs.symm

lemma rayDirection_abs (θ : UnitAddCircle) (i : Fin 2) :
    |rayDirection θ i|≤1 := by
  have hh : ‖fourier 1 θ‖=1 := by simp [fourier_apply,Circle.norm_coe]
  fin_cases i
  · exact (Complex.abs_re_le_norm (fourier 1 θ)).trans_eq hh
  · exact (Complex.abs_im_le_norm (fourier 1 θ)).trans_eq hh

lemma rayDenominator_lower {w : ℝ} (hw : 0<w) (hw' : w≤1) (θ : UnitAddCircle) :
    1/2≤rayDenominator w θ := by
  have h0 : |rayDirection θ 0|≤rayDenominator w θ := by
    apply le_trans _ (le_max_left _ _)
    exact (le_div_iff₀ hw).mpr (mul_le_of_le_one_right (abs_nonneg _) hw')
  have h1 : |rayDirection θ 1|≤rayDenominator w θ := le_max_right _ _
  have hd : 0≤rayDenominator w θ := (abs_nonneg _).trans h1
  have hh := rayDirection_unit θ
  have h0' := sq_abs (rayDirection θ 0)
  have h1' := sq_abs (rayDirection θ 1)
  nlinarith [sq_nonneg (rayDenominator w θ-|rayDirection θ 0|),
    sq_nonneg (rayDenominator w θ-|rayDirection θ 1|),
    mul_self_le_mul_self (abs_nonneg _) h0,mul_self_le_mul_self (abs_nonneg _) h1]

lemma continuous_rayDirection : Continuous rayDirection := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact Complex.continuous_re.comp (fourier 1).continuous
  · exact Complex.continuous_im.comp (fourier 1).continuous

lemma continuous_rectangularRay {w : ℝ} (hw : 0<w) (hw' : w≤1) :
    Continuous (rectangularRay w) := by
  have hd : Continuous (rayDenominator w) :=
    (((continuous_apply 0).comp continuous_rayDirection).abs.div_const w).max
      (((continuous_apply 1).comp continuous_rayDirection).abs)
  apply continuous_pi
  intro i
  exact (((continuous_apply i).comp continuous_rayDirection).div hd
    (fun θ => ne_of_gt (lt_of_lt_of_le (by norm_num) (rayDenominator_lower hw hw' θ))))

lemma fourier_one_translation_bound (θ : UnitAddCircle) (t : ℝ) :
    ‖fourier 1 (θ+(t:UnitAddCircle))-fourier 1 θ‖≤2*Real.pi*|t| := by
  have he : fourier 1 (θ+(t:UnitAddCircle))=fourier 1 θ*fourier 1 (t:UnitAddCircle) := by
    simp [fourier_apply,AddCircle.toCircle_add,Circle.coe_mul]
  rw [he,←mul_sub_one,norm_mul]
  have hh : ‖fourier 1 θ‖=1 := by simp [fourier_apply,Circle.norm_coe]
  rw [hh,one_mul,fourier_coe_apply]
  have hx := Real.norm_exp_I_mul_ofReal_sub_one_le (x:=2*Real.pi*t)
  have he' : (2*Real.pi*Complex.I*(1:ℤ)*(t:ℂ))=
      Complex.I*((2*Real.pi*t:ℝ):ℂ) := by push_cast; ring
  rw [←he'] at hx
  simpa only [Int.cast_one,Complex.ofReal_one,mul_one,div_one,Real.norm_eq_abs,abs_mul,
    abs_of_pos Real.pi_pos,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] using hx

lemma rayDirection_difference (θ : UnitAddCircle) (t : ℝ) (i : Fin 2) :
    |rayDirection (θ+(t:UnitAddCircle)) i-rayDirection θ i|≤2*Real.pi*|t| := by
  apply le_trans _ (fourier_one_translation_bound θ t)
  fin_cases i
  · simpa [rayDirection] using Complex.abs_re_le_norm
      (fourier 1 (θ+(t:UnitAddCircle))-fourier 1 θ)
  · simpa [rayDirection] using Complex.abs_im_le_norm
      (fourier 1 (θ+(t:UnitAddCircle))-fourier 1 θ)

lemma rayDenominator_difference {w : ℝ} (hw : 0<w) (hw' : w≤1)
    (θ : UnitAddCircle) (t : ℝ) :
    |rayDenominator w (θ+(t:UnitAddCircle))-rayDenominator w θ|≤
      (2*Real.pi*|t|)/w := by
  apply (abs_max_sub_max_le_max _ _ _ _).trans
  apply max_le
  · rw [←sub_div,abs_div,abs_of_pos hw]
    exact div_le_div_of_nonneg_right ((abs_abs_sub_abs_le _ _).trans
      (rayDirection_difference θ t 0)) hw.le
  · apply ((abs_abs_sub_abs_le _ _).trans (rayDirection_difference θ t 1)).trans
    exact (le_div_iff₀ hw).mpr (mul_le_of_le_one_right (by positivity) hw')

lemma rectangularRay_difference {w : ℝ} (hw : 0<w) (hw' : w≤1)
    (θ : UnitAddCircle) (t : ℝ) (i : Fin 2) :
    |rectangularRay w (θ+(t:UnitAddCircle)) i-rectangularRay w θ i|≤
      (2+4/w)*(2*Real.pi*|t|) := by
  let A := rayDenominator w (θ+(t:UnitAddCircle))
  let B := rayDenominator w θ
  have hA : 1/2≤A := rayDenominator_lower hw hw' _
  have hB : 1/2≤B := rayDenominator_lower hw hw' _
  have hAp : 0<A := by linarith
  have hBp : 0<B := by linarith
  let x := rayDirection (θ+(t:UnitAddCircle)) i
  let y := rayDirection θ i
  let K := 2*Real.pi*|t|
  have hK : 0≤K := by dsimp [K]; positivity
  have hD : |x-y|≤K := rayDirection_difference θ t i
  have hy : |y|≤1 := rayDirection_abs θ i
  have hAB : |A-B|≤K/w := rayDenominator_difference hw hw' θ t
  have he : x/A-y/B=(x-y)/A+y*(B-A)/(A*B) := by field_simp; ring
  change |x/A-y/B|≤(2+4/w)*K
  rw [he]
  apply (abs_add_le _ _).trans
  have hb1 : |(x-y)/A|≤2*K := by
    rw [abs_div,abs_of_pos hAp]
    apply (div_le_iff₀ hAp).mpr
    nlinarith [mul_nonneg hK (sub_nonneg.mpr hA)]
  have hb2 : |y*(B-A)/(A*B)|≤4*(K/w) := by
    rw [abs_div,abs_mul,abs_sub_comm,abs_of_pos (mul_pos hAp hBp)]
    apply (div_le_iff₀ (mul_pos hAp hBp)).mpr
    have hh := mul_le_mul hy hAB (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    have hAB' : 1/4≤A*B := by nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]
    have hKw : 0≤K/w := div_nonneg hK hw.le
    nlinarith [mul_nonneg hKw (sub_nonneg.mpr hAB')]
  calc
    _≤2*K+4*(K/w) := add_le_add hb1 hb2
    _=(2+4/w)*K := by ring

end ScalarConductivity

end

end OAI
