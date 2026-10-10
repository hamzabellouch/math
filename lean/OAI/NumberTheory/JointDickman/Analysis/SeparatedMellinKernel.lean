import OAI.NumberTheory.JointDickman.Analysis.MellinSieveProfile
import OAI.NumberTheory.TwoPointCorrelations.MRTSampling
import Mathlib.Analysis.Real.Pi.Bounds

namespace OAI

/-! # Quadratic-decay kernels on separated frequency samples -/
namespace JointDickman
open Finset MeasureTheory TwoPointCorrelations

lemma separated_cauchy_kernel_sum (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) (t : ℝ) :
    (∑ u ∈ S, 1/(1+(u-t)^2)) ≤ 8 := by
  let F : ℝ → ℝ := fun x => 1/(1+(x-t)^2)
  let F' : ℝ → ℝ := fun x => -2*(x-t)/(1+(x-t)^2)^2
  have hD (x : ℝ) : 0 < 1+(x-t)^2 := by positivity
  have hF : Continuous F := continuous_const.div
    (continuous_const.add ((continuous_id.sub continuous_const).pow 2))
    (fun x => (hD x).ne')
  have hder (x : ℝ) : HasDerivAt F (F' x) x := by
    have hh := ((hasDerivAt_id x).sub_const t).pow 2
    have hi := (hh.const_add 1).inv (hD x).ne'
    convert hi using 1
    · funext y
      simp [F, one_div]
    · dsimp [F']
      ring
  have hb (x : ℝ) : |F' x| ≤ F x := by
    dsimp [F', F]
    rw [abs_div, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_pow, abs_of_pos (hD x)]
    apply (div_le_div_iff₀ (sq_pos_of_pos (hD x)) (hD x)).mpr
    have ha := sq_nonneg (|x-t|-1)
    rw [sub_sq, sq_abs] at ha
    nlinarith [hD x]
  have hval (u : ℝ) : F u ≤ ∫ x in u..(u+1), 2*F x := by
    have hh := mrt_value_le_unit_integral F F' F hF hder hF
      (fun x => by dsimp [F]; positivity) hb u
    convert hh using 1
    congr 1
    funext x
    ring
  let M : ℝ := (∑ u ∈ S, |u|)+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hrange : ∀ u ∈ S, -M ≤ u ∧ u+1 ≤ M := by
    intro u hu
    have hh : |u| ≤ ∑ v ∈ S, |v| := single_le_sum (fun v _ => abs_nonneg v) hu
    have hh' := abs_le.mp hh
    dsimp [M]
    constructor <;> linarith
  have hs := mrt_sum_unit_integrals_le S (fun x => 2*F x) (hF.const_mul 2)
    (fun x => by dsimp [F]; positivity) hsep (-M) M (by linarith) hrange
  have hint : (∫ x in -M..M, F x) ≤ Real.pi := by
    change (∫ x in -M..M, (fun y : ℝ => 1/(1+y^2)) (x-t)) ≤ _
    rw [intervalIntegral.integral_comp_sub_right (fun y : ℝ => 1/(1+y^2)) t, integral_one_div_one_add_sq]
    linarith [Real.arctan_lt_pi_div_two (M-t), Real.neg_pi_div_two_lt_arctan (-M-t)]
  calc
    _ = ∑ u ∈ S, F u := rfl
    _ ≤ ∑ u ∈ S, ∫ x in u..(u+1), 2*F x := sum_le_sum fun u _ => hval u
    _ ≤ ∫ x in -M..M, 2*F x := hs
    _ = 2*(∫ x in -M..M, F x) := intervalIntegral.integral_const_mul _ _
    _ ≤ 2*Real.pi := mul_le_mul_of_nonneg_left hint (by norm_num)
    _ ≤ 8 := by linarith [Real.pi_lt_four]

lemma separated_mellin_profile_rows (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) {N : ℝ} (hN : 0 ≤ N) (t : ℝ) :
    (∑ u ∈ S, 4*N/(4+(t-u)^2)) ≤ 32*N := by
  calc
    _ ≤ ∑ u ∈ S, 4*N*(1/(1+(u-t)^2)) := by
      apply sum_le_sum
      intro u _
      rw [mul_one_div, show (t-u)^2 = (u-t)^2 by ring]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      linarith
    _ = 4*N*(∑ u ∈ S, 1/(1+(u-t)^2)) := (mul_sum _ _ _).symm
    _ ≤ 4*N*8 := mul_le_mul_of_nonneg_left (separated_cauchy_kernel_sum S hsep t)
      (by positivity)
    _ = _ := by ring

end JointDickman

end OAI
