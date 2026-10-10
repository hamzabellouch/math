import OAI.Geometry.IsometricImmersion.Pulses.PulseCurvaturePrincipal
import OAI.Geometry.IsometricImmersion.Pulses.PulseDerivativeBounds
import OAI.Geometry.IsometricImmersion.Energy.WeightPrimitive
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem coordPartial_xi_eq_line_deriv {f : Coord → ℝ}
    (hf : Differentiable ℝ f) (p : Coord) :
    coordPartial 0 f p = deriv (fun x => f (coordinatePoint x (p 1))) (p 0) := by
  have h := (hf (coordinatePoint (p 0) (p 1))).hasFDerivAt.comp_hasDerivAt
    (p 0) (point_hasDerivAt_t (p 0) (p 1))
  simpa only [point_eta,coordPartial,Function.comp_def] using h.deriv.symm

theorem pulseLine_hasDerivAt (a : ℝ) (N : ℕ) (delta tau x y : ℝ) :
    HasDerivAt (fun u => pulseScalar a N delta tau (coordinatePoint u y))
      ((1/tau^N)*temporalCutoff (tau*y/delta)*
        (deriv (axisBump a) x*Real.cos (tau*x)-tau*axisBump a x*Real.sin (tau*x))) x := by
  have hχ := ((axisBump_contDiff a).differentiable (by simp) x).hasDerivAt
  have hc := (Real.hasDerivAt_cos (tau*x)).comp x ((hasDerivAt_id x).const_mul tau)
  have h := (((hχ.const_mul (1/tau^N)).mul_const
    (temporalCutoff (tau*y/delta))).mul hc)
  simp only [Function.comp_def, Pi.mul_def, mul_one] at h
  convert h using 1 <;>
    (first | rfl | (funext u; simp [pulseScalar, coordinatePoint]) | ring)

theorem pulseScalar_xi (a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) :
    coordPartial 0 (pulseScalar a N delta tau) p =
      (1/tau^N)*temporalCutoff (tau*p 1/delta)*
        (deriv (axisBump a) (p 0)*Real.cos (tau*p 0)-
          tau*axisBump a (p 0)*Real.sin (tau*p 0)) := by
  rw [coordPartial_xi_eq_line_deriv ((pulseScalar_contDiff a N delta tau).differentiable (by simp))]
  exact (pulseLine_hasDerivAt a N delta tau (p 0) (p 1)).deriv

theorem pulseXiLine_hasDerivAt (a : ℝ) (N : ℕ) (delta tau x y : ℝ) :
    HasDerivAt
      (fun u => (1/tau^N)*temporalCutoff (tau*y/delta)*
        (deriv (axisBump a) u*Real.cos (tau*u)-tau*axisBump a u*Real.sin (tau*u)))
      ((1/tau^N)*temporalCutoff (tau*y/delta)*
        (deriv (deriv (axisBump a)) x*Real.cos (tau*x)-
          2*tau*deriv (axisBump a) x*Real.sin (tau*x)-
            tau^2*axisBump a x*Real.cos (tau*x))) x := by
  have hχ := ((axisBump_contDiff a).differentiable (by simp) x).hasDerivAt
  have hχ' := (((contDiff_infty_iff_deriv.mp (axisBump_contDiff a)).2).differentiable
    (by simp) x).hasDerivAt
  have hc := (Real.hasDerivAt_cos (tau*x)).comp x ((hasDerivAt_id x).const_mul tau)
  have hs := (Real.hasDerivAt_sin (tau*x)).comp x ((hasDerivAt_id x).const_mul tau)
  have h := (((hχ'.mul hc).sub ((hχ.const_mul tau).mul hs)).const_mul
    ((1/tau^N)*temporalCutoff (tau*y/delta)))
  simp only [Function.comp_def, Pi.mul_def, Pi.sub_def, mul_one] at h
  convert h using 1
  first | rfl | ring

theorem pulseScalar_xixi (a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) :
    coordPartial 0 (coordPartial 0 (pulseScalar a N delta tau)) p =
      (1/tau^N)*temporalCutoff (tau*p 1/delta)*
        (deriv (deriv (axisBump a)) (p 0)*Real.cos (tau*p 0)-
          2*tau*deriv (axisBump a) (p 0)*Real.sin (tau*p 0)-
            tau^2*axisBump a (p 0)*Real.cos (tau*p 0)) := by
  have hf : ContDiff ℝ ∞ (coordPartial 0 (pulseScalar a N delta tau)) :=
    contDiffOn_univ.mp (partial_contDiffOn
      (pulseScalar_contDiff a N delta tau).contDiffOn isOpen_univ 0)
  rw [coordPartial_xi_eq_line_deriv (hf.differentiable (by simp))]
  have he : (fun x => coordPartial 0 (pulseScalar a N delta tau) (coordinatePoint x (p 1))) =
      (fun x => (1/tau^N)*temporalCutoff (tau*p 1/delta)*
        (deriv (axisBump a) x*Real.cos (tau*x)-tau*axisBump a x*Real.sin (tau*x))) := by
    funext x
    rw [pulseScalar_xi]
    simp [coordinatePoint]
  rw [he]
  exact (pulseXiLine_hasDerivAt a N delta tau (p 0) (p 1)).deriv

def pulsePrincipalLeading (a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) : ℝ :=
  (tau^2/(2*tau^N))*axisBump a (p 0)*temporalCutoff (tau*p 1/delta)*Real.cos (tau*p 0)

def pulsePrincipalRemainder (a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) : ℝ :=
  (1/tau^N)*temporalCutoff (tau*p 1/delta)*
    (tau*deriv (axisBump a) (p 0)*Real.sin (tau*p 0)-
      (1/2 : ℝ)*deriv (deriv (axisBump a)) (p 0)*Real.cos (tau*p 0))

theorem pulse_principal_exact (a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) :
    -(1/2 : ℝ)*coordPartial 0 (coordPartial 0 (pulseScalar a N delta tau)) p =
      pulsePrincipalLeading a N delta tau p + pulsePrincipalRemainder a N delta tau p := by
  rw [pulseScalar_xixi]
  unfold pulsePrincipalLeading pulsePrincipalRemainder
  ring

def pulsePrincipalRemainderBound (a : ℝ) (ha : 0 < a) : ℝ :=
  axisBumpDerivativeBound (1/2) (by norm_num) 0 *
    (axisBumpDerivativeBound a ha 1+axisBumpDerivativeBound a ha 2)

theorem pulsePrincipalRemainderBound_nonneg (a : ℝ) (ha : 0 < a) :
    0 ≤ pulsePrincipalRemainderBound a ha := by
  exact mul_nonneg (axisBumpDerivativeBound_pos (by norm_num) 0).le
    (add_nonneg (axisBumpDerivativeBound_pos ha 1).le (axisBumpDerivativeBound_pos ha 2).le)

theorem pulse_principal_remainder_le {a : ℝ} (ha : 0 < a) (N : ℕ)
    (delta : ℝ) {tau : ℝ} (ht : 1 ≤ tau) (p : Coord) :
    |pulsePrincipalRemainder a N delta tau p| ≤
      pulsePrincipalRemainderBound a ha * tau/tau^N := by
  let A1 := axisBumpDerivativeBound a ha 1
  let A2 := axisBumpDerivativeBound a ha 2
  let P0 := axisBumpDerivativeBound (1/2) (by norm_num) 0
  have hA1 : 0 ≤ A1 := (axisBumpDerivativeBound_pos ha 1).le
  have hA2 : 0 ≤ A2 := (axisBumpDerivativeBound_pos ha 2).le
  have hP0 : 0 ≤ P0 := (axisBumpDerivativeBound_pos (by norm_num) 0).le
  have ht0 : 0 < tau := zero_lt_one.trans_le ht
  have hq : 0 ≤ (1/tau^N) := div_nonneg zero_le_one (pow_nonneg ht0.le N)
  have hχ1 : |deriv (axisBump a) (p 0)| ≤ A1 := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_one,Real.norm_eq_abs]
      using axisBump_derivative_le ha 1 (p 0)
  have hχ2 : |deriv (deriv (axisBump a)) (p 0)| ≤ A2 := by
    simpa only [A2,norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      show 2=1+1 by omega,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero,Real.norm_eq_abs]
      using axisBump_derivative_le ha 2 (p 0)
  have hφ : |temporalCutoff (tau*p 1/delta)| ≤ P0 := by
    simpa only [P0,temporalCutoff,norm_iteratedFDeriv_zero,Real.norm_eq_abs]
      using axisBump_derivative_le (by norm_num : (0 : ℝ)<1/2) 0 (tau*p 1/delta)
  have hinner : |tau*deriv (axisBump a) (p 0)*Real.sin (tau*p 0)-
      (1/2 : ℝ)*deriv (deriv (axisBump a)) (p 0)*Real.cos (tau*p 0)| ≤ tau*(A1+A2) := by
    calc
      _ ≤ |tau*deriv (axisBump a) (p 0)*Real.sin (tau*p 0)|+
          |(1/2 : ℝ)*deriv (deriv (axisBump a)) (p 0)*Real.cos (tau*p 0)| := abs_sub _ _
      _ = tau*|deriv (axisBump a) (p 0)| *|Real.sin (tau*p 0)|+
          (1/2 : ℝ)*|deriv (deriv (axisBump a)) (p 0)| *|Real.cos (tau*p 0)| := by
        simp only [abs_mul,abs_of_pos ht0]
        norm_num
      _ ≤ tau*A1*1+(1/2 : ℝ)*A2*1 := by
        exact add_le_add
          (mul_le_mul (mul_le_mul_of_nonneg_left hχ1 ht0.le) (Real.abs_sin_le_one _)
            (abs_nonneg _) (mul_nonneg ht0.le hA1))
          (mul_le_mul (mul_le_mul_of_nonneg_left hχ2 (by norm_num)) (Real.abs_cos_le_one _)
            (abs_nonneg _) (mul_nonneg (by norm_num) hA2))
      _ ≤ tau*(A1+A2) := by nlinarith [mul_le_mul_of_nonneg_right ht hA2]
  calc
    _ = (1/tau^N)*|temporalCutoff (tau*p 1/delta)| *
        |tau*deriv (axisBump a) (p 0)*Real.sin (tau*p 0)-
          (1/2 : ℝ)*deriv (deriv (axisBump a)) (p 0)*Real.cos (tau*p 0)| := by
      simp only [pulsePrincipalRemainder,abs_mul,abs_of_nonneg hq]
    _ ≤ ((1/tau^N)*P0)*(tau*(A1+A2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hφ hq) hinner (abs_nonneg _)
        (mul_nonneg hq hP0)
    _ = pulsePrincipalRemainderBound a ha*tau/tau^N := by
      dsimp only [A1,A2,P0,pulsePrincipalRemainderBound]
      ring

end SmoothLocal.Pulse

end

end OAI
