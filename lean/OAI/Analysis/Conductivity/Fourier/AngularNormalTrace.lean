import Mathlib
import OAI.Analysis.Conductivity.Sobolev.IntervalTraceEnergy
import OAI.Analysis.Conductivity.Sources.AngularTrace

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

def sourceAngularVelocity (x : UnitAddTorus (Fin 2)) : Fin 3 → ℝ :=
  let z := sourceRayCoordinates x
  ![-sourceLength*z 2*z 0,-z 2*z 1,-z 3]

lemma sourceAngular_affine (t a : ℝ) (x : UnitAddTorus (Fin 2)) :
    sourceAngularCollar (t+a) x=sourceAngularCollar t x+a • sourceAngularVelocity x := by
  ext i
  fin_cases i <;> simp [sourceAngularCollar,sourceAngularPolynomial,sourceAngularVelocity] <;> ring

lemma sourceAngularVelocity_norm (x : UnitAddTorus (Fin 2)) : ‖sourceAngularVelocity x‖≤8 := by
  have hz := sourceRayCoordinates_mem x
  have hb (i : Fin 4) : |sourceRayCoordinates x i|≤2 := abs_le.mpr ⟨hz.1 i,hz.2 i⟩
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤8)).mpr
  intro i
  fin_cases i <;> simp [sourceAngularVelocity,Real.norm_eq_abs]
  · have hh := mul_le_mul (hb 2) (hb 0) (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
    norm_num [sourceLength] at *
    nlinarith [abs_nonneg (sourceRayCoordinates x 2*sourceRayCoordinates x 0)]
  · have hh := mul_le_mul (hb 2) (hb 1) (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
    linarith
  · linarith [hb 3]

lemma continuous_sourceAngularVelocity : Continuous sourceAngularVelocity := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [sourceAngularVelocity]
  · exact (continuous_const.mul ((continuous_apply (2 : Fin 4)).comp continuous_sourceRayCoordinates)).mul
      ((continuous_apply (0 : Fin 4)).comp continuous_sourceRayCoordinates)
  · exact (((continuous_apply (2 : Fin 4)).comp continuous_sourceRayCoordinates).neg).mul
      ((continuous_apply (1 : Fin 4)).comp continuous_sourceRayCoordinates)
  · exact ((continuous_apply (3 : Fin 4)).comp continuous_sourceRayCoordinates).neg

lemma sourceAngular_normal_deriv {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (t a : ℝ) (x : UnitAddTorus (Fin 2)) :
    deriv (fun s => f (sourceAngularCollar (t+s) x)) a=
      fderiv ℝ f (sourceAngularCollar (t+a) x) (sourceAngularVelocity x) := by
  have hd := (((hf.differentiable (by simp) (sourceAngularCollar t x+a • sourceAngularVelocity x)).hasFDerivAt).comp_hasDerivAt a
    (((hasDerivAt_id a).smul_const (sourceAngularVelocity x)).const_add (sourceAngularCollar t x))).deriv
  change deriv (fun s : ℝ => f (sourceAngularCollar t x+s • sourceAngularVelocity x)) a=_ at hd
  simpa only [sourceAngular_affine,one_smul] using hd

theorem sourceAngular_pointwise_trace {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (t : ℝ) {η : ℝ} (hη : 0<η)
    (x : UnitAddTorus (Fin 2)) :
    (f (sourceAngularCollar t x))^2≤(1+1/η)*(∫ a in (0:ℝ)..η,
      64*‖fderiv ℝ f (sourceAngularCollar (t+a) x)‖^2+
        2*(f (sourceAngularCollar (t+a) x))^2) := by
  have hq : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun a : ℝ => f (sourceAngularCollar (t+a) x)) := by
    simp_rw [sourceAngular_affine]
    exact hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hh := fourier_mode_trace_energy hq hη (m:=1) (by norm_num)
  simp only [add_zero,one_pow,one_mul] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply intervalIntegral.integral_mono_on hη.le
  · exact (((hq.continuous_deriv (by simp)).pow 2).add
      (continuous_const.mul (hq.continuous.pow 2))).intervalIntegrable _ _
  · have hc : Continuous (fun a : ℝ => sourceAngularCollar (t+a) x) := by
      simp_rw [sourceAngular_affine]; fun_prop
    exact ((continuous_const.mul ((hf.continuous_fderiv (by simp)).comp hc |>.norm.pow 2)).add
      (continuous_const.mul (hq.continuous.pow 2))).intervalIntegrable _ _
  · intro a _
    rw [sourceAngular_normal_deriv hf]
    have hb := (fderiv ℝ f (sourceAngularCollar (t+a) x)).le_opNorm (sourceAngularVelocity x)
    have hb' := hb.trans (mul_le_mul_of_nonneg_left (sourceAngularVelocity_norm x) (norm_nonneg _))
    have hs := mul_self_le_mul_self (norm_nonneg _) hb'
    simp only [Real.norm_eq_abs,←pow_two,sq_abs] at hs
    nlinarith

lemma rayDirection_coe_angle (a : ℝ) :
    rayDirection ((a/(2*Real.pi):ℝ):UnitAddCircle)=![Real.cos a,Real.sin a] := by
  have he : fourier 1 ((a/(2*Real.pi):ℝ):UnitAddCircle)=Complex.exp ((a:ℂ)*Complex.I) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    have hp : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    field_simp
  ext i
  fin_cases i
  · simp [rayDirection,he]
  · simp [rayDirection,he]

lemma rectangularRay_of_direction {w k : ℝ} (hw : 0<w) (hk : 0<k)
    (θ : UnitAddCircle) (j : Fin 4) {b : ℝ} (hb : |b|≤1)
    (he : rayDirection θ=k • ![w*squareFace j b 0,squareFace j b 1]) :
    rectangularRay w θ=![w*squareFace j b 0,squareFace j b 1] := by
  have hd : rayDenominator w θ=k := by
    dsimp [rayDenominator]
    rw [he]
    simp only [Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one,
      abs_mul,abs_of_pos hk,abs_of_pos hw]
    have he' : k*(w*|squareFace j b 0|)/w=k*|squareFace j b 0| := by field_simp
    rw [he',←mul_max_of_nonneg _ _ hk.le,squareFace_max j hb,mul_one]
  ext i
  rw [rectangularRay,he,hd]
  simp only [Pi.smul_apply,smul_eq_mul]
  exact mul_div_cancel_left₀ _ hk.ne'

def faceRayAngle (w : ℝ) (j : Fin 4) (b : ℝ) : ℝ :=
  ![Real.arctan (b/w),Real.pi/2+Real.arctan (w*b),
    Real.pi+Real.arctan (b/w),3*Real.pi/2+Real.arctan (w*b)] j/(2*Real.pi)

lemma faceRayAngle_image {w : ℝ} (hw : 0<w) (j : Fin 4) {b : ℝ} (hb : |b|≤1) :
    rectangularRay w ((faceRayAngle w j b:ℝ):UnitAddCircle)=
      ![w*squareFace j b 0,squareFace j b 1] := by
  have hp (x : ℝ) : 0<Real.sqrt (1+x^2) := Real.sqrt_pos.mpr (by positivity)
  fin_cases j
  · apply rectangularRay_of_direction hw (k:=(w*Real.sqrt (1+(b/w)^2))⁻¹)
      (inv_pos.mpr (mul_pos hw (hp _))) _ 0 hb
    dsimp only [faceRayAngle]
    rw [rayDirection_coe_angle]
    ext i; fin_cases i <;> simp [squareFace,squareFaceBase,squareFaceDirection,
      Real.cos_arctan,Real.sin_arctan] <;> field_simp
  · apply rectangularRay_of_direction hw (k:=(Real.sqrt (1+(w*b)^2))⁻¹)
      (inv_pos.mpr (hp _)) _ 1 hb
    dsimp only [faceRayAngle]
    rw [rayDirection_coe_angle]
    ext i; fin_cases i <;> simp [squareFace,squareFaceBase,squareFaceDirection,
      Real.cos_add,Real.sin_add,Real.cos_arctan,Real.sin_arctan]; ring
  · apply rectangularRay_of_direction hw (k:=(w*Real.sqrt (1+(b/w)^2))⁻¹)
      (inv_pos.mpr (mul_pos hw (hp _))) _ 2 hb
    dsimp only [faceRayAngle]
    rw [rayDirection_coe_angle]
    ext i; fin_cases i <;> simp [squareFace,squareFaceBase,squareFaceDirection,
      Real.cos_add,Real.sin_add,Real.cos_arctan,Real.sin_arctan] <;> field_simp
  · apply rectangularRay_of_direction hw (k:=(Real.sqrt (1+(w*b)^2))⁻¹)
      (inv_pos.mpr (hp _)) _ 3 hb
    dsimp only [faceRayAngle]
    rw [rayDirection_coe_angle]
    have he : 3*Real.pi/2=Real.pi+Real.pi/2 := by ring
    rw [he]
    ext i; fin_cases i <;> simp [squareFace,squareFaceBase,squareFaceDirection,
      Real.cos_add,Real.sin_add,Real.cos_arctan,Real.sin_arctan]; ring

lemma faceRayAngle_endpoints {w : ℝ} (hw : 0<w) :
    (∀ j : Fin 3,faceRayAngle w j.castSucc 1=faceRayAngle w j.succ (-1)) ∧
    faceRayAngle w 3 1=faceRayAngle w 0 (-1)+1 := by
  have hx := Real.arctan_inv_of_pos hw
  constructor
  · intro j
    fin_cases j <;> simp [faceRayAngle,one_div,neg_div,Real.arctan_neg,hx] <;> ring
  · simp [faceRayAngle,one_div,neg_div,Real.arctan_neg,hx]
    field_simp
    ring

def faceRayDensity (w : ℝ) (j : Fin 4) (b : ℝ) : ℝ :=
  ![(1/(1+(b/w)^2))/w,w/(1+(w*b)^2),
    (1/(1+(b/w)^2))/w,w/(1+(w*b)^2)] j/(2*Real.pi)

lemma hasDerivAt_faceRayAngle (w : ℝ) (j : Fin 4) (b : ℝ) :
    HasDerivAt (faceRayAngle w j) (faceRayDensity w j b) b := by
  have h0 := ((Real.hasDerivAt_arctan (b/w)).comp b ((hasDerivAt_id b).div_const w)).div_const (2*Real.pi)
  have h1 := (((Real.hasDerivAt_arctan (w*b)).comp b ((hasDerivAt_id b).const_mul w)).const_add (Real.pi/2)).div_const (2*Real.pi)
  have h2 := (((Real.hasDerivAt_arctan (b/w)).comp b ((hasDerivAt_id b).div_const w)).const_add Real.pi).div_const (2*Real.pi)
  have h3 := (((Real.hasDerivAt_arctan (w*b)).comp b ((hasDerivAt_id b).const_mul w)).const_add (3*Real.pi/2)).div_const (2*Real.pi)
  unfold faceRayAngle faceRayDensity
  fin_cases j
  · simpa [faceRayAngle,faceRayDensity,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using h0
  · simpa [faceRayAngle,faceRayDensity,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using h1
  · simpa [faceRayAngle,faceRayDensity,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using h2
  · simpa [faceRayAngle,faceRayDensity,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using h3

lemma continuous_faceRayDensity (w : ℝ) (j : Fin 4) : Continuous (faceRayDensity w j) := by
  have h0 : Continuous (fun b : ℝ => (1/(1+(b/w)^2))/w/(2*Real.pi)) := by
    have hd : Continuous (fun b : ℝ => 1+(b/w)^2) := by fun_prop
    exact ((continuous_const.div hd (fun b => ne_of_gt (by positivity))).div_const w).div_const _
  have h1 : Continuous (fun b : ℝ => (w/(1+(w*b)^2))/(2*Real.pi)) := by
    have hd : Continuous (fun b : ℝ => 1+(w*b)^2) := by fun_prop
    exact (continuous_const.div hd (fun b => ne_of_gt (by positivity))).div_const _
  fin_cases j
  · exact h0
  · exact h1
  · exact h0
  · exact h1

lemma faceRayDensity_bounds {w : ℝ} (hw : 0<w) (hw' : w≤1) (j : Fin 4) (b : ℝ) :
    0≤faceRayDensity w j b ∧ faceRayDensity w j b≤(1/w)/(2*Real.pi) := by
  have hp : 0<2*Real.pi := by positivity
  have H0 : 0≤(1/(1+(b/w)^2))/w ∧ (1/(1+(b/w)^2))/w≤1/w := by
    constructor
    · positivity
    · exact div_le_div_of_nonneg_right (by apply div_le_one_of_le₀; nlinarith; positivity) hw.le
  have H1 : 0≤w/(1+(w*b)^2) ∧ w/(1+(w*b)^2)≤1/w := by
    constructor
    · positivity
    · have hh : w/(1+(w*b)^2)≤w := div_le_self hw.le (by nlinarith [sq_nonneg (w*b)])
      apply hh.trans
      apply (le_div_iff₀ hw).mpr
      nlinarith
  fin_cases j
  · exact ⟨div_nonneg H0.1 hp.le,div_le_div_of_nonneg_right H0.2 hp.le⟩
  · exact ⟨div_nonneg H1.1 hp.le,div_le_div_of_nonneg_right H1.2 hp.le⟩
  · exact ⟨div_nonneg H0.1 hp.le,div_le_div_of_nonneg_right H0.2 hp.le⟩
  · exact ⟨div_nonneg H1.1 hp.le,div_le_div_of_nonneg_right H1.2 hp.le⟩

end ScalarConductivity

end

end OAI
