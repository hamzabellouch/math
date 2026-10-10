import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselGaussianSlope
import Mathlib.Analysis.Real.Pi.Bounds

namespace OAI

/-! Numerical derivative bounds for the two actual arithmetic frequency scales. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaWhittakerDerivative_simple_tail {r : ℝ} (hr : 0<r)
    (hx : 4≤4*Real.pi*r) :
    ‖cubicThetaWhittakerDerivative r‖≤3*Real.pi*r*Real.exp (-4*Real.pi*r) := by
  let b := (4*Real.pi*r-1)/2-1/18
  have hb : 0<b := by dsimp [b]; linarith
  have hs : Real.sqrt (Real.pi/b)≤3/2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    apply (div_le_iff₀ hb).mpr
    dsimp [b]
    nlinarith [Real.pi_lt_d2]
  have h := cubicThetaWhittakerDerivative_gaussian hr (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hs
    (show 0≤(4*Real.pi*r/2)*Real.exp (-4*Real.pi*r) by positivity)
  exact h.trans (hmul.trans_eq (by ring))

lemma cubicThetaFrequency_scalar_lower :
    (241/100:ℝ)≤4*Real.pi*Real.sqrt 3/9 ∧
    (29/4:ℝ)≤4*Real.pi*Real.sqrt 3/3 := by
  have hs : (1732/1000:ℝ)≤Real.sqrt 3 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h := mul_le_mul Real.pi_gt_d4.le hs (by positivity) (by positivity)
  constructor <;> nlinarith

lemma cubicThetaPrimary_derivative_tail {N : ℝ} (hN : 4≤N) :
    (81/2:ℝ)*(Real.sqrt 3*Real.sqrt N/9)*
      ‖cubicThetaWhittakerDerivative (Real.sqrt 3*Real.sqrt N/9)‖≤
      (9/2:ℝ)*Real.pi*(N*Real.exp (-(241/100:ℝ)*Real.sqrt N)) := by
  let r := Real.sqrt 3*Real.sqrt N/9
  have hN0 : 0<N := by linarith
  have hr : 0<r := by dsimp [r]; positivity
  have hsN : 2≤Real.sqrt N := by
    convert Real.sqrt_le_sqrt hN using 1
    norm_num
  have hscale := cubicThetaFrequency_scalar_lower.1
  have harg : (241/100:ℝ)*Real.sqrt N≤4*Real.pi*r := by
    have h := mul_le_mul_of_nonneg_right hscale (Real.sqrt_nonneg N)
    dsimp [r]
    nlinarith
  have hx : 4≤4*Real.pi*r := by nlinarith
  have hr2 : r^2=N/27 := by
    dsimp [r]
    rw [div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sq_sqrt hN0.le]
    ring
  have h := mul_le_mul_of_nonneg_left (cubicThetaWhittakerDerivative_simple_tail hr hx)
    (show 0≤(81/2:ℝ)*r by positivity)
  have he := Real.exp_le_exp.mpr (neg_le_neg harg)
  calc
    _ ≤ (81/2:ℝ)*r*(3*Real.pi*r*Real.exp (-4*Real.pi*r)) := h
    _ = (243/2:ℝ)*Real.pi*r^2*Real.exp (-4*Real.pi*r) := by ring
    _ = (9/2:ℝ)*Real.pi*(N*Real.exp (-4*Real.pi*r)) := by rw [hr2]; ring
    _ = ((9/2:ℝ)*Real.pi*N)*Real.exp (-(4*Real.pi*r)) := by ring_nf
    _ ≤ ((9/2:ℝ)*Real.pi*N)*Real.exp (-((241/100:ℝ)*Real.sqrt N)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring_nf

lemma cubicThetaRamified_derivative_tail {N : ℝ} (hN : 1≤N) :
    27*(Real.sqrt 3*Real.sqrt N/3)*
      ‖cubicThetaWhittakerDerivative (Real.sqrt 3*Real.sqrt N/3)‖≤
      27*Real.pi*(N*Real.exp (-(29/4:ℝ)*Real.sqrt N)) := by
  let r := Real.sqrt 3*Real.sqrt N/3
  have hN0 : 0<N := by linarith
  have hr : 0<r := by dsimp [r]; positivity
  have hsN : 1≤Real.sqrt N := by simpa using Real.sqrt_le_sqrt hN
  have hscale := cubicThetaFrequency_scalar_lower.2
  have harg : (29/4:ℝ)*Real.sqrt N≤4*Real.pi*r := by
    have h := mul_le_mul_of_nonneg_right hscale (Real.sqrt_nonneg N)
    dsimp [r]
    nlinarith
  have hx : 4≤4*Real.pi*r := by nlinarith
  have hr2 : r^2=N/3 := by
    dsimp [r]
    rw [div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sq_sqrt hN0.le]
    ring
  have h := mul_le_mul_of_nonneg_left (cubicThetaWhittakerDerivative_simple_tail hr hx)
    (show 0≤(27:ℝ)*r by positivity)
  have he := Real.exp_le_exp.mpr (neg_le_neg harg)
  calc
    _ ≤ 27*r*(3*Real.pi*r*Real.exp (-4*Real.pi*r)) := h
    _ = 81*Real.pi*r^2*Real.exp (-4*Real.pi*r) := by ring
    _ = 27*Real.pi*(N*Real.exp (-4*Real.pi*r)) := by rw [hr2]; ring
    _ = (27*Real.pi*N)*Real.exp (-(4*Real.pi*r)) := by ring_nf
    _ ≤ (27*Real.pi*N)*Real.exp (-((29/4:ℝ)*Real.sqrt N)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring_nf

end CubicFirstMoment

end

end OAI
