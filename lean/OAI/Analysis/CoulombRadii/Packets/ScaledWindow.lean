import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.Space

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

def scaledWindow (g : 𝓢(Space,ℝ)) (a : ℝ) (ha : a ≠ 0) : 𝓢(Space,ℝ) :=
  (Real.sqrt (a^3))⁻¹ • SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (ContinuousLinearEquiv.smulLeft (Units.mk0 a⁻¹ (inv_ne_zero ha))) g

@[simp] lemma scaledWindow_apply (g : 𝓢(Space,ℝ)) (a : ℝ) (ha : a ≠ 0) (x : Space) :
    scaledWindow g a ha x = (Real.sqrt (a^3))⁻¹*g (a⁻¹ • x) := rfl

lemma space_integral_inv_smul (f : Space → ℝ) {a : ℝ} (ha : 0 < a) :
    (∫ x, f (a⁻¹ • x)) = a^3*(∫ x, f x) := by
  rw [Measure.integral_comp_smul_of_nonneg volume f a⁻¹ (hR := inv_nonneg.mpr ha.le)]
  simp [finrank_euclideanSpace, smul_eq_mul]

lemma scaledWindow_mass (g : 𝓢(Space,ℝ)) {a : ℝ} (ha : 0 < a) :
    (∫ x : Space, scaledWindow g a ha.ne' x^2) = ∫ x : Space, g x^2 := by
  simp only [scaledWindow_apply,mul_pow,inv_pow]
  rw [Real.sq_sqrt (by positivity), integral_const_mul,space_integral_inv_smul (fun x => g x^2) ha]
  field_simp

lemma scaledWindow_fderiv (g : 𝓢(Space,ℝ)) {a : ℝ} (ha : 0 < a) (x v : Space) :
    fderiv ℝ (scaledWindow g a ha.ne') x v =
      (Real.sqrt (a^3))⁻¹*a⁻¹*(fderiv ℝ g (a⁻¹ • x) v) := by
  have hd := (g.differentiableAt (x := a⁻¹ • x)).hasFDerivAt.comp x
    ((a⁻¹ • ContinuousLinearMap.id ℝ Space).hasFDerivAt)
  have H := (hd.const_mul (Real.sqrt (a^3))⁻¹).fderiv
  change fderiv ℝ (fun z => (Real.sqrt (a^3))⁻¹*g (a⁻¹ • z)) x v = _
  simp only [Function.comp_def] at H
  rw [H]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.map_smul,smul_eq_mul]
  ring

lemma scaledWindow_kinetic (g : 𝓢(Space,ℝ)) {a : ℝ} (ha : 0 < a) :
    (∑ b : Fin 3, ∫ x : Space, (fderiv ℝ (scaledWindow g a ha.ne') x (EuclideanSpace.single b 1))^2) =
      (∑ b : Fin 3, ∫ x : Space, (fderiv ℝ g x (EuclideanSpace.single b 1))^2)/a^2 := by
  simp only [scaledWindow_fderiv g ha,mul_pow,inv_pow]
  rw [Real.sq_sqrt (by positivity)]
  simp_rw [integral_const_mul]
  have hi (b : Fin 3) := space_integral_inv_smul
    (fun x => (fderiv ℝ g x (EuclideanSpace.single b 1))^2) ha
  simp_rw [hi, ←mul_assoc]
  rw [←Finset.mul_sum]
  field_simp

lemma scaledWindow_support (g : 𝓢(Space,ℝ)) (hgs : ∀ z, 1 < ‖z‖ → g z = 0)
    {a : ℝ} (ha : 0 < a) (x : Space) (hx : a < ‖x‖) :
    scaledWindow g a ha.ne' x = 0 := by
  rw [scaledWindow_apply,hgs,mul_zero]
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]
  exact (one_lt_inv_mul₀ ha).2 hx

lemma scaledWindow_compactSupport (g : 𝓢(Space,ℝ))
    (hgs : ∀ z, 1 < ‖z‖ → g z = 0) {a : ℝ} (ha : 0 < a) :
    HasCompactSupport (scaledWindow g a ha.ne' : Space → ℝ) := by
  apply HasCompactSupport.intro (K := Metric.closedBall 0 a) (isCompact_closedBall 0 a)
  intro x hx
  exact scaledWindow_support g hgs ha x (by simpa [Metric.mem_closedBall] using hx)

lemma scaledWindow_radial (g : 𝓢(Space,ℝ))
    (hrad : ∀ z, g z = g (EuclideanSpace.single 0 ‖z‖)) {a : ℝ} (ha : 0 < a) (x : Space) :
    scaledWindow g a ha.ne' x = scaledWindow g a ha.ne' (EuclideanSpace.single 0 ‖x‖) := by
  simp only [scaledWindow_apply]
  congr 1
  rw [hrad (a⁻¹ • x)]
  congr 1
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]
  symm
  ext i
  simp only [PiLp.smul_apply,PiLp.single_apply,smul_eq_mul]
  split <;> simp_all

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise ContDiff
namespace Coulomb

def windowSeed (x : Space) : ℝ := Real.smoothTransition (2*(1-‖x‖^2))

lemma windowSeed_smooth : ContDiff ℝ ∞ windowSeed := by
  apply Real.smoothTransition.contDiff.comp
  exact contDiff_const.mul (contDiff_const.sub (contDiff_norm_sq ℝ))

lemma windowSeed_support (x : Space) (hx : 1 ≤ ‖x‖) : windowSeed x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  nlinarith [norm_nonneg x]

lemma windowSeed_compact : HasCompactSupport windowSeed := by
  apply HasCompactSupport.intro (K := Metric.closedBall 0 1) (isCompact_closedBall 0 1)
  intro x hx
  apply windowSeed_support x
  have hx' : 1 < ‖x‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hx
  exact hx'.le

lemma windowSeed_mass_pos : 0 < ∫ x : Space, windowSeed x^2 := by
  apply integral_pos_of_integrable_nonneg_nonzero
    (windowSeed_smooth.continuous.pow 2)
    ((windowSeed_smooth.continuous.pow 2).integrable_of_hasCompactSupport (by simpa only [pow_two] using (windowSeed_compact.mul_left (f := windowSeed))))
    (fun x => sq_nonneg _) (x := 0)
  norm_num [windowSeed, Real.smoothTransition.one_of_one_le]

def unitWindow : 𝓢(Space,ℝ) :=
  (Real.sqrt (∫ x : Space, windowSeed x^2))⁻¹ •
    windowSeed_compact.toSchwartzMap windowSeed_smooth

lemma unitWindow_apply (x : Space) : unitWindow x =
    (Real.sqrt (∫ z : Space, windowSeed z^2))⁻¹*windowSeed x := rfl

lemma unitWindow_mass : (∫ x : Space, unitWindow x^2) = 1 := by
  simp only [unitWindow_apply,mul_pow,inv_pow]
  rw [Real.sq_sqrt windowSeed_mass_pos.le,integral_const_mul,inv_mul_cancel₀ windowSeed_mass_pos.ne']

lemma unitWindow_support (x : Space) (hx : 1 < ‖x‖) : unitWindow x = 0 := by
  rw [unitWindow_apply,windowSeed_support x hx.le,mul_zero]

lemma unitWindow_radial (x : Space) : unitWindow x = unitWindow (EuclideanSpace.single 0 ‖x‖) := by
  simp [unitWindow_apply,windowSeed,PiLp.norm_single]

lemma unitWindow_kinetic_nonneg :
    0 ≤ ∑ b : Fin 3, ∫ x : Space, (fderiv ℝ unitWindow x (EuclideanSpace.single b 1))^2 := by
  exact Finset.sum_nonneg (fun b hb => integral_nonneg (fun x => sq_nonneg _))

end Coulomb

end

end OAI
