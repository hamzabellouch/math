import Mathlib
import OAI.Probability.SphericalField.Heat.Tilt

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

lemma heatTilt_affine_sub_bound (s d : ℝ≥0) (f h k : ℝ →ᵇ ℝ) (t x : ℝ) :
    |heatTilt s d (f+t • h) k x - heatTilt s d f k x| ≤
      2*(d:ℝ)*‖h‖*‖k‖*|t| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (fun u _ => (heatTilt_directional_deriv s d f h k u x).hasDerivWithinAt)
    (fun u _ => heatTilt_directional_bound s d f h k u x) convex_univ
    (mem_univ (0:ℝ)) (mem_univ t)
  simpa only [zero_smul,add_zero,sub_zero,Real.norm_eq_abs] using hh

lemma heatLog_terminal_quadratic_error (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (x : ℝ) :
    |heatLog s d (f+h) x - heatLog s d f x - heatTilt s d f h x| ≤
      2*(d:ℝ)*‖h‖^2 := by
  have hd (u : ℝ) : HasDerivAt
      (fun t => heatLog s d (f+t • h) x - heatLog s d f x - t*heatTilt s d f h x)
      (heatTilt s d (f+u • h) h x - heatTilt s d f h x) u := by
    convert! ((heatLog_directional_deriv s d f h u x).sub_const (heatLog s d f x)).sub
      ((hasDerivAt_id u).mul_const (heatTilt s d f h x)) using 1
    simp
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun u _ => (hd u).hasDerivWithinAt) (fun u hu => show
      ‖heatTilt s d (f+u • h) h x - heatTilt s d f h x‖ ≤ 2*(d:ℝ)*‖h‖^2 from by
        calc
          _ ≤ 2*(d:ℝ)*‖h‖*‖h‖*|u| := heatTilt_affine_sub_bound s d f h h u x
          _ ≤ 2*(d:ℝ)*‖h‖^2 := by
            rw [abs_of_nonneg hu.1]
            nlinarith [mul_nonneg (show 0 ≤ 2*(d:ℝ)*‖h‖^2 by positivity) (sub_nonneg.mpr hu.2.le)])
  simpa only [zero_smul,one_smul,add_zero,zero_mul,one_mul,sub_self,sub_zero,
    Real.norm_eq_abs] using hh

lemma heatTilt_continuous (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) : Continuous (heatTilt s d f h) :=
  (gaussianAverage_continuous s (expBCF d f*h)).div
    (gaussianAverage_continuous s (expBCF d f)) (fun x => (gaussianAverage_exp_pos s d f x).ne')

def heatTiltBCF (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨heatTilt s d f h,heatTilt_continuous s d f h⟩
    (2*‖h‖) (fun x y => by
      change |heatTilt s d f h x - heatTilt s d f h y| ≤ 2*‖h‖
      exact (abs_sub _ _).trans (by linarith [heatTilt_abs_le s d f h x,heatTilt_abs_le s d f h y]))

@[simp] lemma heatTiltBCF_apply (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (x : ℝ) :
    heatTiltBCF s d f h x = heatTilt s d f h x := rfl

lemma heatTiltBCF_norm_le (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) : ‖heatTiltBCF s d f h‖ ≤ ‖h‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg h)).mpr (heatTilt_abs_le s d f h)

def heatTiltCLM (s d : ℝ≥0) (f : ℝ →ᵇ ℝ) : (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := heatTiltBCF s d f
      map_add' := fun h k => by ext x; exact heatTilt_add s d f h k x
      map_smul' := fun a h => by ext x; exact heatTilt_smul s d f h a x }
    1 (fun h => by
      change ‖heatTiltBCF s d f h‖ ≤ 1*‖h‖
      simpa only [one_mul] using heatTiltBCF_norm_le s d f h)

lemma heatLogBCF_terminal_quadratic_error (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) :
    ‖heatLogBCF s d (f+h)-heatLogBCF s d f-heatTiltCLM s d f h‖ ≤ 2*(d:ℝ)*‖h‖^2 :=
  (BoundedContinuousFunction.norm_le (by positivity)).mpr (heatLog_terminal_quadratic_error s d f h)

lemma heatLogBCF_hasFDerivAt (s d : ℝ≥0) (f : ℝ →ᵇ ℝ) :
    HasFDerivAt (heatLogBCF s d) (heatTiltCLM s d f) f := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro ε hε
  have he : ∀ᶠ h : (ℝ →ᵇ ℝ) in 𝓝 0, ‖h‖ < ε/(2*(d:ℝ)+1) :=
    by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ →ᵇ ℝ)
        (show 0 < ε/(2*(d:ℝ)+1) by positivity)] with h hh
      simpa only [Metric.mem_ball,dist_zero_right] using hh
  filter_upwards [he] with h hh
  calc
    _ ≤ 2*(d:ℝ)*‖h‖^2 := heatLogBCF_terminal_quadratic_error s d f h
    _ ≤ ε*‖h‖ := by
      have hb : ‖h‖*(2*(d:ℝ)+1) < ε := (lt_div_iff₀ (by positivity)).mp hh
      nlinarith [norm_nonneg h,mul_nonneg (norm_nonneg h) (sub_nonneg.mpr hb.le)]

def shiftBCF (f : ℝ →ᵇ ℝ) (a : ℝ) : ℝ →ᵇ ℝ :=
  f.compContinuous ⟨fun x => x+a,by fun_prop⟩

end SphericalPerceptron
end
end
end

end OAI
