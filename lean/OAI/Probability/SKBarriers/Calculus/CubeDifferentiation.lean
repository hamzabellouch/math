import Mathlib
import OAI.Probability.SKBarriers.Calculus.ParameterCalculus

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

theorem cubeIntegral_congr_parameter (n : ℕ) (f g : ParameterSpace n → ℝ)
    (a b x : ℝ) (he : ∀ z, parameter n z = x → f z = g z) :
    cubeIntegral n f a b x = cubeIntegral n g a b x := by
  induction n with
  | zero => exact he x rfl
  | succ n ih =>
    apply ih
    intro z hz
    apply intervalIntegral.integral_congr
    intro y _
    exact he (z,y) hz

theorem cubeIntegral_pos (n : ℕ) (f : ParameterSpace n → ℝ)
    (hf : Continuous f) (hpos : ∀ z, 0 < f z) {a b : ℝ} (hab : a < b) (x : ℝ) :
    0 < cubeIntegral n f a b x := by
  induction n with
  | zero => exact hpos x
  | succ n ih =>
    apply ih _ (contDiff_zero.mp (contDiff_intervalIntegral 0 f (contDiff_zero.mpr hf) a b))
    intro z
    apply intervalIntegral.integral_pos hab
      (hf.comp (continuous_const.prodMk continuous_id)).continuousOn
    · exact fun y _ => (hpos (z,y)).le
    · exact ⟨a, ⟨le_rfl, hab.le⟩, hpos (z,a)⟩

theorem cubeIntegral_const_mul (n : ℕ) (f : ParameterSpace n → ℝ) (c a b x : ℝ) :
    cubeIntegral n (fun z => c*f z) a b x = c*cubeIntegral n f a b x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change cubeIntegral n (fun z => ∫ y in a..b, c*f (z,y)) a b x = _
    simp_rw [intervalIntegral.integral_const_mul]
    exact ih _

theorem cubeIntegral_sub (n : ℕ) (f g : ParameterSpace n → ℝ)
    (hf : Continuous f) (hg : Continuous g) (a b x : ℝ) :
    cubeIntegral n (fun z => f z-g z) a b x = cubeIntegral n f a b x-cubeIntegral n g a b x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hiF (z : ParameterSpace n) : IntervalIntegrable (fun y => f (z,y)) volume a b :=
      (hf.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
    have hiG (z : ParameterSpace n) : IntervalIntegrable (fun y => g (z,y)) volume a b :=
      (hg.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
    change cubeIntegral n (fun z => ∫ y in a..b, f (z,y)-g (z,y)) a b x = _
    simp_rw [intervalIntegral.integral_sub (hiF _) (hiG _)]
    exact ih _ _ (contDiff_zero.mp (contDiff_intervalIntegral 0 f (contDiff_zero.mpr hf) a b))
      (contDiff_zero.mp (contDiff_intervalIntegral 0 g (contDiff_zero.mpr hg) a b))

theorem cubePotential_exp_eq (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) {a b : ℝ} (hab : a < b) (x : ℝ) :
    Real.exp (-cubePotential n V a b x) = cubeIntegral n (fun z => Real.exp (-V z)) a b x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Real.exp (-cubePotential n (marginalPotential V a b) a b x) = _
    rw [ih _ (contDiff_marginalPotential _ 2 hV hab)]
    congr 1
    funext z
    dsimp only [marginalPotential]
    have hc : Continuous (fun y => V (z,y)) :=
      hV.continuous.comp (continuous_const.prodMk continuous_id)
    rw [neg_neg, Real.exp_log (intervalPartition_pos hc hab)]
    rfl

theorem cubePotential_eq_neg_log (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) {a b : ℝ} (hab : a < b) :
    cubePotential n V a b = fun x => -Real.log (cubeIntegral n (fun z => Real.exp (-V z)) a b x) := by
  funext x
  rw [← cubePotential_exp_eq n V hV hab x, Real.log_exp, neg_neg]

theorem contDiff_cubePotential (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) {a b : ℝ} (hab : a < b) :
    ContDiff ℝ 2 (cubePotential n V a b) := by
  induction n with
  | zero => exact hV
  | succ n ih => exact ih _ (contDiff_marginalPotential _ 2 hV hab)

theorem contDiff_parameterDerivative (n : ℕ) (f : ParameterSpace n → ℝ)
    (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (parameterDerivative n f) :=
  (hf.fderiv_right (by norm_num)).clm_apply contDiff_const

theorem cubePotential_hessian_formula (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) {a b : ℝ} (hab : a < b) (x : ℝ) :
    let w := fun z => Real.exp (-V z)
    let Z := cubeIntegral n w a b x
    let Z₁ := cubeIntegral n (parameterDerivative n w) a b x
    let Z₂ := cubeIntegral n (parameterDerivative n (parameterDerivative n w)) a b x
    Hessian (cubePotential n V a b) x 1 1 = (Z₁/Z)^2-Z₂/Z := by
  let w : ParameterSpace n → ℝ := fun z => Real.exp (-V z)
  have hw : ContDiff ℝ 2 w := hV.neg.exp
  let Z := cubeIntegral n w a b
  let Z₁ := cubeIntegral n (parameterDerivative n w) a b
  let Z₂ := cubeIntegral n (parameterDerivative n (parameterDerivative n w)) a b
  have hZpos (t : ℝ) : 0 < Z t := cubeIntegral_pos n w hw.continuous
    (fun _ => Real.exp_pos _) hab t
  have hD (t : ℝ) : HasDerivAt Z (Z₁ t) t :=
    hasDerivAt_cubeIntegral n w (hw.of_le (by norm_num)) a b t
  have hD₁ (t : ℝ) : HasDerivAt Z₁ (Z₂ t) t :=
    hasDerivAt_cubeIntegral n _ (contDiff_parameterDerivative n w hw) a b t
  have hM (t : ℝ) : HasDerivAt (cubePotential n V a b) (-(Z₁ t/Z t)) t := by
    rw [cubePotential_eq_neg_log n V hV hab]
    exact ((hD t).log (ne_of_gt (hZpos t))).neg
  have he : (fun t => fderiv ℝ (cubePotential n V a b) t 1) = fun t => -(Z₁ t/Z t) := by
    funext t
    exact (hM t).deriv
  have hH := hasDerivAt_score_comp (cubePotential n V a b)
    (contDiff_cubePotential n V hV hab) (hasDerivAt_id x) 1
  change HasDerivAt (fun t => fderiv ℝ (cubePotential n V a b) t 1)
    (Hessian (cubePotential n V a b) x 1 1) x at hH
  rw [he] at hH
  have hq := ((hD₁ x).div (hD x) (ne_of_gt (hZpos x))).neg
  have hh := hH.unique hq
  change Hessian (cubePotential n V a b) x 1 1 = (Z₁ x/Z x)^2-Z₂ x/Z x
  rw [hh]
  field_simp
  ring

end SK.Analytic

end
end
end
end
end

end OAI
