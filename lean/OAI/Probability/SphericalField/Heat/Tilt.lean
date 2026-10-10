import Mathlib
import OAI.Probability.SphericalField.Heat.Derivatives
import OAI.Probability.SphericalField.Gibbs.Tilting

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

def heatTilt (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (x : ℝ) : ℝ :=
  gaussianAverage s (expBCF d f * h) x / gaussianAverage s (expBCF d f) x

lemma heatTilt_zero (s : ℝ≥0) (f h : ℝ →ᵇ ℝ) (x : ℝ) :
    heatTilt s 0 f h x = gaussianAverage s h x := by
  simp [heatTilt,gaussianAverage,expBCF]

lemma gaussianAverage_affine (s : ℝ≥0) (f h : ℝ →ᵇ ℝ) (t x : ℝ) :
    gaussianAverage s (f+t • h : ℝ →ᵇ ℝ) x = gaussianAverage s f x + t * gaussianAverage s h x := by
  simp only [gaussianAverage,BoundedContinuousFunction.coe_add,
    BoundedContinuousFunction.coe_smul,Pi.add_apply,smul_eq_mul]
  rw [integral_add (gaussianAverage_integrable s f x)
    ((gaussianAverage_integrable s h x).const_mul t), integral_const_mul]

lemma gaussian_exp_affine_deriv (s : ℝ≥0) (d : ℝ) (f h : ℝ →ᵇ ℝ) (t x : ℝ) :
    HasDerivAt (fun u : ℝ => gaussianAverage s (expBCF d (f+u • h)) x)
      (d * gaussianAverage s (expBCF d (f+t • h) * h) x) t := by
  have hv : Measurable (fun z : ℝ => d*h (x+z)) := by fun_prop
  have hF : Measurable (fun z : ℝ => Real.exp (d*f (x+z))) := by fun_prop
  have hh := tilt_integral_deriv (gaussianReal 0 s) hv hF
    (mul_nonneg (abs_nonneg d) (norm_nonneg h)) (Real.exp_pos (|d| * ‖f‖)).le
    (fun z => by
      change |d*h (x+z)| ≤ |d| * ‖h‖
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using h.norm_coe_le_norm (x+z)) (abs_nonneg d))
    (fun z => exp_bcf_bound d f (x+z)) t
  convert! hh using 1
  · ext u
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [expBCF,BoundedContinuousFunction.mkOfBound_coe,
      ContinuousMap.coe_mk,BoundedContinuousFunction.coe_add,
      BoundedContinuousFunction.coe_smul,Pi.add_apply,smul_eq_mul]
    rw [← Real.exp_add]
    congr 1
    ring
  · unfold gaussianAverage
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [Pi.mul_apply,
      expBCF,BoundedContinuousFunction.mkOfBound_coe,ContinuousMap.coe_mk,
      BoundedContinuousFunction.coe_add,BoundedContinuousFunction.coe_smul,
      Pi.add_apply,smul_eq_mul]
    rw [show d*(f (x+z)+t*h (x+z))=t*(d*h (x+z))+d*f (x+z) by ring,Real.exp_add]
    ring

lemma heatLog_directional_deriv (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (t x : ℝ) :
    HasDerivAt (fun u : ℝ => heatLog s d (f+u • h) x)
      (heatTilt s d (f+t • h) h x) t := by
  by_cases hd : d = 0
  · subst d
    simp only [heatTilt_zero,heatLog,↓reduceIte,gaussianAverage_affine]
    convert! (hasDerivAt_const t (gaussianAverage s f x)).add
      ((hasDerivAt_id t).mul_const (gaussianAverage s h x)) using 1
    simp
  · have hh := ((gaussian_exp_affine_deriv s d f h t x).log
      (gaussianAverage_exp_pos s d (f+t • h) x).ne').const_mul (d:ℝ)⁻¹
    convert! hh using 1
    · simp only [heatLog,hd,↓reduceIte]
    · unfold heatTilt
      field_simp [NNReal.coe_ne_zero.mpr hd]

lemma gaussianAverage_add (s : ℝ≥0) (f h : ℝ →ᵇ ℝ) (x : ℝ) :
    gaussianAverage s (f+h : ℝ →ᵇ ℝ) x = gaussianAverage s f x + gaussianAverage s h x :=
  integral_add (gaussianAverage_integrable s f x) (gaussianAverage_integrable s h x)

lemma gaussianAverage_smul (s : ℝ≥0) (f : ℝ →ᵇ ℝ) (a x : ℝ) :
    gaussianAverage s (a • f : ℝ →ᵇ ℝ) x = a * gaussianAverage s f x := by
  exact integral_const_mul _ _

lemma heatTilt_add (s d : ℝ≥0) (f h k : ℝ →ᵇ ℝ) (x : ℝ) :
    heatTilt s d f (h+k) x = heatTilt s d f h x + heatTilt s d f k x := by
  unfold heatTilt
  change gaussianAverage s (expBCF d f * (h+k) : ℝ →ᵇ ℝ) x / _ = _
  rw [mul_add,gaussianAverage_add,add_div]
  rfl

lemma heatTilt_smul (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (a x : ℝ) :
    heatTilt s d f (a • h) x = a * heatTilt s d f h x := by
  unfold heatTilt
  change gaussianAverage s (expBCF d f * (a • h) : ℝ →ᵇ ℝ) x / _ = _
  rw [mul_smul_comm,gaussianAverage_smul,mul_div_assoc]
  rfl

lemma heatTilt_const (s d : ℝ≥0) (f : ℝ →ᵇ ℝ) (a x : ℝ) :
    heatTilt s d f (BoundedContinuousFunction.const ℝ a) x = a := by
  unfold heatTilt gaussianAverage
  simp only [Pi.mul_apply,BoundedContinuousFunction.const_apply]
  rw [integral_mul_const]
  exact mul_div_cancel_left₀ a (gaussianAverage_exp_pos s d f x).ne'

lemma heatTilt_nonneg (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (hh : ∀ x, 0 ≤ h x) (x : ℝ) :
    0 ≤ heatTilt s d f h x := by
  apply div_nonneg (integral_nonneg fun z => mul_nonneg (Real.exp_pos _).le (hh _))
    (gaussianAverage_exp_pos s d f x).le

lemma heatTilt_mono (s d : ℝ≥0) (f h k : ℝ →ᵇ ℝ)
    (hh : ∀ x, h x ≤ k x) (x : ℝ) : heatTilt s d f h x ≤ heatTilt s d f k x := by
  apply div_le_div_of_nonneg_right _ (gaussianAverage_exp_pos s d f x).le
  exact integral_mono (gaussianAverage_integrable s (expBCF d f*h) x)
    (gaussianAverage_integrable s (expBCF d f*k) x)
    (fun z => mul_le_mul_of_nonneg_left (hh _) (Real.exp_pos _).le)

lemma heatTilt_abs_le (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (x : ℝ) :
    |heatTilt s d f h x| ≤ ‖h‖ := by
  rw [abs_le]
  constructor
  · have hh := heatTilt_mono s d f (BoundedContinuousFunction.const ℝ (-‖h‖)) h
      (fun y => (abs_le.mp (h.norm_coe_le_norm y)).1) x
    simpa only [heatTilt_const] using hh
  · have hh := heatTilt_mono s d f h (BoundedContinuousFunction.const ℝ ‖h‖)
      (fun y => (abs_le.mp (h.norm_coe_le_norm y)).2) x
    simpa only [heatTilt_const] using hh

lemma heatTilt_sq (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (x : ℝ) :
    (heatTilt s d f h x)^2 ≤ heatTilt s d f (h^2) x := by
  let c := heatTilt s d f h x
  have hp := heatTilt_nonneg s d f ((h-BoundedContinuousFunction.const ℝ c)^2)
    (fun y => sq_nonneg _) x
  have he : (h-BoundedContinuousFunction.const ℝ c)^2 =
      h^2 + (-2*c) • h + BoundedContinuousFunction.const ℝ (c^2) := by
    ext y
    simp only [BoundedContinuousFunction.coe_pow,BoundedContinuousFunction.coe_sub,
      BoundedContinuousFunction.coe_add,BoundedContinuousFunction.coe_smul,
      BoundedContinuousFunction.const_apply,Pi.pow_apply,Pi.sub_apply,Pi.add_apply,smul_eq_mul]
    ring
  rw [he,heatTilt_add,heatTilt_add,heatTilt_smul,heatTilt_const] at hp
  dsimp only [c] at hp
  nlinarith

lemma Jet3.heatLog_d1 (g : Jet3) (s d : ℝ≥0) (x : ℝ) :
    (g.heatLog s d).d1 x = heatTilt s d g.f g.d1 x := by
  by_cases hd : d = 0
  · subst d
    simp only [Jet3.heatLog,↓reduceDIte,heatTilt_zero]
    rfl
  · have he : (g.exp d).d1 = (d:ℝ) • (expBCF d g.f*g.d1) := rfl
    simp only [Jet3.heatLog,hd,↓reduceDIte,Jet3.heatLogPos]
    change (d:ℝ)⁻¹ * (SphericalPerceptron.gaussianAverage s (g.exp d).d1 x *
      (SphericalPerceptron.gaussianAverage s (expBCF d g.f) x)⁻¹) = _
    rw [he,SphericalPerceptron.gaussianAverage_smul]
    unfold heatTilt
    field_simp [NNReal.coe_ne_zero.mpr hd]
    rfl

lemma Jet3.heatLog_d1_sq_le (g : Jet3) (s d : ℝ≥0) (x : ℝ) :
    ((g.heatLog s d).d1 x)^2 ≤ heatTilt s d g.f (g.d1^2) x := by
  rw [g.heatLog_d1]
  exact heatTilt_sq s d g.f g.d1 x

lemma gaussian_exp_affine_mul_deriv (s : ℝ≥0) (d : ℝ) (f h k : ℝ →ᵇ ℝ) (t x : ℝ) :
    HasDerivAt (fun u : ℝ => gaussianAverage s (expBCF d (f+u • h)*k : ℝ →ᵇ ℝ) x)
      (d * gaussianAverage s (expBCF d (f+t • h) * (h*k) : ℝ →ᵇ ℝ) x) t := by
  have hv : Measurable (fun z : ℝ => d*h (x+z)) := by fun_prop
  have hF : Measurable (fun z : ℝ => Real.exp (d*f (x+z))*k (x+z)) := by fun_prop
  have hh := tilt_integral_deriv (gaussianReal 0 s) hv hF
    (mul_nonneg (abs_nonneg d) (norm_nonneg h))
    (mul_nonneg (Real.exp_pos (|d| * ‖f‖)).le (norm_nonneg k))
    (fun z => by
      change |d*h (x+z)| ≤ |d| * ‖h‖
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using h.norm_coe_le_norm (x+z)) (abs_nonneg d))
    (fun z => by
      rw [abs_mul]
      exact mul_le_mul (exp_bcf_bound d f (x+z)) (k.norm_coe_le_norm (x+z))
        (abs_nonneg _) (Real.exp_pos _).le) t
  convert! hh using 1
  · ext u
    apply integral_congr_ae
    filter_upwards [] with z
    change Real.exp (d*(f (x+z)+u*h (x+z)))*k (x+z) = _
    rw [show d*(f (x+z)+u*h (x+z))=u*(d*h (x+z))+d*f (x+z) by ring,Real.exp_add]
    ring
  · unfold gaussianAverage
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    change d*(Real.exp (d*(f (x+z)+t*h (x+z)))*(h (x+z)*k (x+z))) = _
    rw [show d*(f (x+z)+t*h (x+z))=t*(d*h (x+z))+d*f (x+z) by ring,Real.exp_add]
    ring

lemma heatTilt_directional_deriv (s d : ℝ≥0) (f h k : ℝ →ᵇ ℝ) (t x : ℝ) :
    HasDerivAt (fun u : ℝ => heatTilt s d (f+u • h) k x)
      ((d:ℝ)*(heatTilt s d (f+t • h) (h*k) x -
        heatTilt s d (f+t • h) h x * heatTilt s d (f+t • h) k x)) t := by
  have hh := (gaussian_exp_affine_mul_deriv s d f h k t x).div
    (gaussian_exp_affine_deriv s d f h t x) (gaussianAverage_exp_pos s d (f+t • h) x).ne'
  convert! hh using 1
  unfold heatTilt
  simp only [← BoundedContinuousFunction.coe_mul]
  field_simp

lemma heatTilt_directional_bound (s d : ℝ≥0) (f h k : ℝ →ᵇ ℝ) (t x : ℝ) :
    |(d:ℝ)*(heatTilt s d (f+t • h) (h*k) x -
        heatTilt s d (f+t • h) h x * heatTilt s d (f+t • h) k x)| ≤
      2*(d:ℝ)*‖h‖*‖k‖ := by
  rw [abs_mul,abs_of_nonneg d.coe_nonneg]
  calc
    _ ≤ (d:ℝ)*(|heatTilt s d (f+t • h) (h*k) x| +
        |heatTilt s d (f+t • h) h x * heatTilt s d (f+t • h) k x|) := by
      gcongr; exact abs_sub _ _
    _ ≤ (d:ℝ)*(‖h*k‖ + ‖h‖*‖k‖) := by
      rw [abs_mul]
      gcongr
      · exact heatTilt_abs_le s d _ _ x
      · exact heatTilt_abs_le s d _ _ x
      · exact heatTilt_abs_le s d _ _ x
    _ ≤ 2*(d:ℝ)*‖h‖*‖k‖ := by
      nlinarith [mul_le_mul_of_nonneg_left (norm_mul_le h k) d.coe_nonneg]

end SphericalPerceptron
end
end
end

end OAI
