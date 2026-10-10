import Mathlib
import OAI.Probability.SKSupport.Moments.BurgersJets

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def tanhDrift (c M x : ℝ) : ℝ := c*Real.tanh (M*x)

lemma tanh_scaled_derivative (M x : ℝ) :
    HasDerivAt (fun y => Real.tanh (M*y)) (M*(1-(Real.tanh (M*x))^2)) x := by
  convert (hasDerivAt_tanh (M*x)).comp x ((hasDerivAt_id x).const_mul M) using 1 <;>
    first | rfl | ring

lemma tanhDrift_derivative (c M x : ℝ) :
    HasDerivAt (tanhDrift c M) (c*M*(1-(Real.tanh (M*x))^2)) x := by
  convert (tanh_scaled_derivative M x).const_mul c using 1 <;> first | rfl | ring

lemma tanhDrift_second (c M x : ℝ) :
    iteratedDeriv 2 (tanhDrift c M) x = -2*c*M^2*Real.tanh (M*x)*(1-(Real.tanh (M*x))^2) := by
  have he : deriv (tanhDrift c M) = fun y => c*M*(1-(Real.tanh (M*y))^2) :=
    funext (fun y => (tanhDrift_derivative c M y).deriv)
  rw [iteratedDeriv_succ (n := 1),iteratedDeriv_one,he]
  convert ((((tanh_scaled_derivative M x).pow 2).const_sub 1).const_mul (c*M)).deriv using 1
  ring

lemma tanhDrift_rate (c M x : ℝ) :
    burgersRate (fun _ => tanhDrift c M) 0 x =
      c*M*(c-M)*Real.tanh (M*x)*(1-(Real.tanh (M*x))^2) := by
  rw [burgersRate,tanhDrift_second,(tanhDrift_derivative c M x).deriv]
  dsimp only [tanhDrift]
  ring

lemma tanhDrift_wronskian (c M x : ℝ) :
    backwardWronskian (fun _ => tanhDrift c M) 0 x =
      2*c^2*M^2*(M-c)*(Real.tanh (M*x))^3*(1-(Real.tanh (M*x))^2) := by
  have he : burgersRate (fun _ => tanhDrift c M) 0 = fun y =>
      c*M*(c-M)*Real.tanh (M*y)*(1-(Real.tanh (M*y))^2) := funext (tanhDrift_rate c M)
  have hd := ((tanh_scaled_derivative M x).const_mul (c*M*(c-M))).mul
    (((tanh_scaled_derivative M x).pow 2).const_sub 1)
  have hd' : HasDerivAt (fun y => c*M*(c-M)*Real.tanh (M*y)*(1-(Real.tanh (M*y))^2))
      (c*M^2*(c-M)*(1-(Real.tanh (M*x))^2)*(1-3*(Real.tanh (M*x))^2)) x := by
    convert hd using 1
    simp only [Pi.pow_apply]
    ring
  rw [backwardWronskian,he,hd'.deriv,(tanhDrift_derivative c M x).deriv]
  dsimp only [tanhDrift]
  ring

lemma tanh_sq_gap_pos (y : ℝ) : 0 < 1-(Real.tanh y)^2 := by
  have hh := Real.abs_tanh_lt_one y
  nlinarith [sq_abs (Real.tanh y),abs_nonneg (Real.tanh y)]

lemma tanh_nonneg_of_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ Real.tanh y := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hy) (Real.cosh_pos y).le

lemma tanhDrift_initial_signs {c M : ℝ} (hc : 0 < c) (hM : c ≤ M) (x : ℝ) (hx : 0 ≤ x) :
    iteratedDeriv 2 (tanhDrift c M) x ≤ 0 ∧
    burgersRate (fun _ => tanhDrift c M) 0 x ≤ 0 ∧
    0 ≤ backwardWronskian (fun _ => tanhDrift c M) 0 x := by
  have hMp : 0 < M := hc.trans_le hM
  have hT := tanh_nonneg_of_nonneg (mul_nonneg hMp.le hx)
  have hD := (tanh_sq_gap_pos (M*x)).le
  rw [tanhDrift_second,tanhDrift_rate,tanhDrift_wronskian]
  refine ⟨?_,?_,?_⟩
  · apply mul_nonpos_of_nonpos_of_nonneg _ hD
    apply mul_nonpos_of_nonpos_of_nonneg _ hT
    apply mul_nonpos_of_nonpos_of_nonneg _ (sq_nonneg M)
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) hc.le
  · apply mul_nonpos_of_nonpos_of_nonneg _ hD
    apply mul_nonpos_of_nonpos_of_nonneg _ hT
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hc.le hMp.le) (sub_nonpos.mpr hM)
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hM))
      (pow_nonneg hT _)) hD

lemma gaussianBurgers_terminal {f : ℝ → ℝ} (c : ℝ) :
    gaussianBurgers c f 0 = fun x => c*deriv f x := by
  have he : varianceLogHeat c 0 f = f := funext (fun x => by
    simpa only [backward,sub_self] using backward_terminal c 0 f x)
  funext x
  rw [gaussianBurgers,he]

lemma gaussianBurgers_softAbs_terminal {M : ℝ} (hM : M ≠ 0) (c : ℝ) :
    gaussianBurgers c (softAbs M) 0 = tanhDrift c M := by
  rw [gaussianBurgers_terminal]
  funext x
  rw [(hasDerivAt_softAbs hM x).deriv]
  rfl

end ZeroTemperatureSK.Heat

end
end

end OAI
