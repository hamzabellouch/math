import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianStepCalculus
import OAI.Probability.SKBarriers.Calculus.ParameterLinear

namespace OAI

section

noncomputable section
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem tilted_add_constant {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.tilted (fun x => f x+c) = μ.tilted f := by
  unfold Measure.tilted
  congr 1
  funext x
  simp_rw [Real.exp_add,integral_mul_const]
  rw [mul_div_mul_right _ _ (Real.exp_ne_zero c)]

def gaussianMassBound (B : ℝ) : ℝ :=
  (∫ y : ℝ, Real.exp ((B+2)* |y|) ∂gaussianReal 0 1) /
    (∫ y : ℝ, Real.exp (-B* |y|) ∂gaussianReal 0 1)

theorem gaussianMassBound_pos (B : ℝ) : 0 < gaussianMassBound B :=
  div_pos (integral_exp_pos (integrable_exp_mul_abs_gaussian (B+2)))
    (integral_exp_pos (integrable_exp_mul_abs_gaussian (-B)))

theorem gaussian_tilted_variance_bound {X : ℝ → ℝ} (hX : Continuous X)
    {v B m : ℝ} (hv : 0 ≤ v) (hvB : v ≤ B) (hm : |m| ≤ 1)
    (hb : ∀ y, |X y| ≤ v* |y|) :
    variance X ((gaussianReal 0 1).tilted (fun y => m*X y)) ≤
      gaussianMassBound B*v^2 := by
  let ν := gaussianReal 0 1
  let D := ∫ y : ℝ, Real.exp (-B* |y|) ∂ν
  let A := ∫ y : ℝ, Real.exp ((B+2)* |y|) ∂ν
  let Z := ∫ y, Real.exp (m*X y) ∂ν
  have hB : 0 ≤ B := hv.trans hvB
  have hd : 0 < D := integral_exp_pos (integrable_exp_mul_abs_gaussian (-B))
  have hA : 0 < A := integral_exp_pos (integrable_exp_mul_abs_gaussian (B+2))
  have hmb (y : ℝ) : |m*X y| ≤ B* |y| := by
    rw [abs_mul]
    calc
      |m| * |X y| ≤ |X y| := by nlinarith [abs_nonneg (X y)]
      _ ≤ v* |y| := hb y
      _ ≤ B* |y| := mul_le_mul_of_nonneg_right hvB (abs_nonneg y)
  have he (y : ℝ) : Real.exp (m*X y) ≤ Real.exp (B* |y|) :=
    Real.exp_le_exp.mpr ((le_abs_self _).trans (hmb y))
  have hi : Integrable (fun y => Real.exp (m*X y)) ν := by
    apply (integrable_exp_mul_abs_gaussian B).mono'
      (Real.continuous_exp.comp (continuous_const.mul hX)).aestronglyMeasurable
    exact ae_of_all _ (fun y => by simpa only [Function.comp_apply,Pi.mul_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using he y)
  have hDZ : D ≤ Z := by
    have H := gaussian_exp_integral_bounds (fun y => m*X y) (continuous_const.mul hX) (A := 0) hB
      (fun y => by simpa using hmb y)
    simpa only [neg_zero,Real.exp_zero,one_mul] using H.1
  have hZ : 0 < Z := hd.trans_le hDZ
  let : IsProbabilityMeasure (ν.tilted (fun y => m*X y)) := isProbabilityMeasure_tilted hi
  have hb2 (y : ℝ) : (X y)^2*Real.exp (m*X y) ≤ v^2*Real.exp ((B+2)* |y|) := by
    have hs : (X y)^2 ≤ v^2* |y|^2 := by
      have H := sq_le_sq₀ (abs_nonneg (X y)) (mul_nonneg hv (abs_nonneg y)) |>.mpr (hb y)
      simpa only [sq_abs,mul_pow] using H
    have hy : |y| ≤ Real.exp |y| := (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1)).trans (Real.add_one_le_exp |y|)
    have hy2 : |y|^2 ≤ Real.exp (2* |y|) := by
      rw [show 2* |y| = |y|+|y| by ring,Real.exp_add]
      nlinarith [Real.exp_pos |y|,abs_nonneg y]
    calc
      _ ≤ (v^2* |y|^2)*Real.exp (B* |y|) :=
        mul_le_mul hs (he y) (Real.exp_pos _).le (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ ≤ (v^2*Real.exp (2* |y|))*Real.exp (B* |y|) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hy2 (sq_nonneg v)) (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc,← Real.exp_add]; congr 2; ring
  have hn : (∫ y, (X y)^2*Real.exp (m*X y) ∂ν) ≤ v^2*A := by
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg (ae_of_all _ (fun y => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le))
      ((integrable_exp_mul_abs_gaussian (B+2)).const_mul (v^2)) (ae_of_all _ hb2)
  calc
    _ ≤ ∫ y, (X y)^2 ∂ν.tilted (fun y => m*X y) :=
      variance_le_expectation_sq (hX.aestronglyMeasurable.mono_ac (tilted_absolutelyContinuous _ _))
    _ = (∫ y, (X y)^2*Real.exp (m*X y) ∂ν)/Z := by
      rw [integral_tilted_mul_eq_mgf,← integral_div]
      congr 1
      funext y
      change (Real.exp (m*X y)/Z)*(X y)^2 = _
      ring
    _ ≤ (v^2*A)/Z := div_le_div_of_nonneg_right hn hZ.le
    _ ≤ (v^2*A)/D := div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) hA.le) hd hDZ
    _ = _ := by dsimp [gaussianMassBound,A,D,ν]; ring

section Anchored
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gaussianStepLaw_variance_bound {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (x : E) {v B m : ℝ} (hv : 0 ≤ v) (hvB : v ≤ B) (hm : |m| ≤ 1)
    (hb : ∀ y, |f (x,y)-f (x,0)| ≤ v* |y|) :
    variance (fun y => f (x,y)) (gaussianStepLaw m f x) ≤ gaussianMassBound B*v^2 := by
  let X := fun y => f (x,y)-f (x,0)
  have hX : Continuous X := (hf.1.continuous.comp (continuous_const.prodMk continuous_id)).sub continuous_const
  have he : gaussianStepLaw m f x = (gaussianReal 0 1).tilted (fun y => m*X y) := by
    calc
      _ = (gaussianReal 0 1).tilted (fun y => m*X y+m*f (x,0)) := by
        change (gaussianReal 0 1).tilted (fun y => m*f (x,y)) = _
        apply tilted_congr
        exact ae_of_all _ (fun y => by dsimp [X]; ring)
      _ = _ := tilted_add_constant _ _ _
  let := gaussianStepLaw_probability hf m x
  have hfm : AEStronglyMeasurable (fun y => f (x,y)) (gaussianStepLaw m f x) :=
    (hf.1.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mono_ac
      (tilted_absolutelyContinuous _ _)
  rw [← variance_sub_const hfm (f (x,0)),he]
  exact gaussian_tilted_variance_bound hX hv hvB hm hb

end Anchored

end SK.Analytic

end
end

end OAI
