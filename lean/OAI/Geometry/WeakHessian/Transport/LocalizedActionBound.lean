import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.LocalizedCertificate
import OAI.Geometry.WeakHessian.HeatFlow.PlanHeatEntropy

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology

def localizedActionBound (K a c CG T : ℝ) : ℝ :=
  1-(K-a*c)*T+2*|K-a*c| *T*(localizedHeatM K a CG T-1)+4*(K-a*c)^2*T^2

lemma localizedHeatM_one_le {K a CG T : ℝ} (ha : 0 ≤ a) (hCG : 0 ≤ CG) (hT : 0 ≤ T) :
    1 ≤ localizedHeatM K a CG T := Real.one_le_exp (by positivity)

lemma reciprocal_factor_bound {k t M : ℝ} (ht : 0 ≤ t) (hM : 1 ≤ M) :
    (1+2*max (-k) 0*t*M)/(1+2*max k 0*t/M) ≤
      1-2*k*t+2*|k| *t*(M-1)+4*k^2*t^2 := by
  have hMp : 0 < M := zero_lt_one.trans_le hM
  rcases le_total k 0 with hk | hk
  · rw [max_eq_left (by linarith : 0 ≤ -k), max_eq_right hk,abs_of_nonpos hk]
    simp only [mul_zero,zero_mul,zero_div,add_zero,div_one]
    nlinarith [sq_nonneg (k*t)]
  · rw [max_eq_right (by linarith : -k ≤ 0),max_eq_left hk,abs_of_nonneg hk]
    simp only [mul_zero,zero_mul,add_zero]
    let x := 2*k*t/M
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hrec : 1/(1+x) ≤ 1-x+x^2 := by
      apply (div_le_iff₀ (by positivity : 0 < 1+x)).mpr
      nlinarith [mul_nonneg (sq_nonneg x) hx]
    have hxle : x ≤ 2*k*t := by
      dsimp [x]; apply (div_le_iff₀ hMp).mpr
      nlinarith [mul_nonneg hk ht]
    have hlin : -x ≤ -2*k*t+2*k*t*(M-1) := by
      dsimp [x]
      rw [← neg_div]
      apply (div_le_iff₀ hMp).mpr
      nlinarith [mul_nonneg (by positivity : 0 ≤ 2*k*t) (sq_nonneg (M-1))]
    have hsq : x^2 ≤ (2*k*t)^2 := (sq_le_sq₀ hx (by positivity)).mpr hxle
    change 1/(1+x) ≤ _
    exact hrec.trans (by nlinarith only [hlin,hsq])

lemma localizedHeatFactor_reciprocal_bound {K a c CG t U : ℝ}
    (ha : 0 ≤ a) (hCG : 0 ≤ CG) (ht : 0 ≤ t) (htU : t ≤ U) :
    1/localizedHeatFactor K a c CG t ≤
      1-2*(K-a*c)*t+2*|K-a*c| *U*(localizedHeatM K a CG U-1)+4*(K-a*c)^2*U^2 := by
  have hM := localizedHeatM_one_le (K := K) ha hCG ht
  have hMU : localizedHeatM K a CG t ≤ localizedHeatM K a CG U := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left htU (by positivity)
  have hU : 0 ≤ U := ht.trans htU
  have H := reciprocal_factor_bound (k := K-a*c) ht hM
  have he : 1/localizedHeatFactor K a c CG t =
      (1+2*max (-(K-a*c)) 0*t*localizedHeatM K a CG t)/
        (1+2*max (K-a*c) 0*t/localizedHeatM K a CG t) := by
    dsimp [localizedHeatFactor,localizedHeatDen]
    rw [one_div_div]
  rw [he]
  apply H.trans
  have hprod := mul_le_mul htU (sub_le_sub_right hMU 1) (sub_nonneg.mpr hM) hU
  have hsq := (sq_le_sq₀ ht hU).mpr htU
  have h1 := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 2*|K-a*c|)
  have h2 := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 4*(K-a*c)^2)
  nlinarith only [h1,h2]

lemma localizedHeatFactor_continuousOn (K a c CG : ℝ) :
    ContinuousOn (localizedHeatFactor K a c CG) (Ici 0) := by
  unfold localizedHeatFactor
  apply ContinuousOn.div
  · apply Continuous.continuousOn
    apply continuous_const.add
    exact (by fun_prop : Continuous (fun t : ℝ => 2*max (K-a*c) 0*t)).div
      (show Continuous (fun t : ℝ => localizedHeatM K a CG t) from by unfold localizedHeatM; fun_prop) (fun t => Real.exp_ne_zero _)
  · change ContinuousOn (fun t : ℝ => 1+2*max (-(K-a*c)) 0*t*Real.exp (2*(|K|+a*CG)*t)) (Ici 0)
    fun_prop
  · intro t ht
    exact (zero_lt_one.trans_le (localizedHeatDen_one_le K a c CG ht)).ne'

lemma localized_action_integral_bound {K a c CG δ T E : ℝ}
    (ha : 0 ≤ a) (hCG : 0 ≤ CG) (hδ : 0 ≤ δ) (hT : 0 ≤ T) (hE : 0 ≤ E) :
    (∫ s in (0:ℝ)..1,E/localizedHeatFactor K a c CG (backwardsHeatTime δ T s)/2) ≤
      E/2*(1-2*(K-a*c)*δ-(K-a*c)*T+
        2*|K-a*c| *(δ+T)*(localizedHeatM K a CG (δ+T)-1)+4*(K-a*c)^2*(δ+T)^2) := by
  let U := δ+T
  let A := 2*|K-a*c| *U*(localizedHeatM K a CG U-1)+4*(K-a*c)^2*U^2
  have hθn (s : ℝ) : 0 ≤ backwardsHeatTime δ T s := by
    simp only [backwardsHeatTime]; positivity
  have hθc : Continuous (backwardsHeatTime δ T) := by change Continuous (fun s : ℝ => δ+T*max (1-s) 0); fun_prop
  have hbc := (localizedHeatFactor_continuousOn K a c CG).comp_continuous hθc hθn
  have hic : Continuous (fun s => E/localizedHeatFactor K a c CG (backwardsHeatTime δ T s)/2) :=
    (continuous_const.div hbc (fun s => (localizedHeatFactor_pos K a c CG (hθn s)).ne')).div_const 2
  have hB : Continuous (fun s : ℝ => E/2*(1-2*(K-a*c)*(δ+T*(1-s))+A)) := by fun_prop
  have H := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    (hic.intervalIntegrable (μ := volume) 0 1) (hB.intervalIntegrable (μ := volume) 0 1) (fun s hs => by
      have hθ : backwardsHeatTime δ T s = δ+T*(1-s) := by
        simp only [backwardsHeatTime]; rw [max_eq_left (by linarith [hs.2])]
      have htU : backwardsHeatTime δ T s ≤ U := by rw [hθ]; dsimp [U]; nlinarith [hs.1]
      have H := mul_le_mul_of_nonneg_left
        (localizedHeatFactor_reciprocal_bound (K := K) (c := c) ha hCG (hθn s) htU) (by positivity : 0 ≤ E/2)
      rw [hθ] at H ⊢
      convert H using 1 <;> first | rfl | ((try dsimp only [A]); ring))
  have he (s : ℝ) : E/2*(1-2*(K-a*c)*(δ+T*(1-s))+A) =
      E/2*(1-2*(K-a*c)*δ-2*(K-a*c)*T+A)+E*(K-a*c)*T*s := by ring
  simp_rw [he] at H
  rw [intervalIntegral.integral_add (intervalIntegrable_const) (Continuous.intervalIntegrable (by fun_prop) 0 1),
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,integral_id] at H
  simp only [sub_zero,one_pow,zero_pow (by norm_num : (2:ℕ) ≠ 0),smul_eq_mul,one_mul] at H
  convert H using 1
  first | rfl | ((try dsimp only [A,U]); ring)

end WeakHessian

end
end

end OAI
