import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.ShellBias

namespace OAI

open MeasureTheory Set Filter
open scoped BigOperators ContDiff
noncomputable section
namespace CoulombAtom

lemma shellCutoff_deriv_le {u : ℝ} (hu : 0 < u) (x : Space) (a : Fin 3) :
    |lineDeriv ℝ (shellCutoff hu).value x (spaceDirections a)| ≤
      2*(Real.pi*smoothTransitionBound)/u := by
  change |lineDeriv ℝ (fun y => (radialOutside 0 hu.le hu).value y*
    (radialInside 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u)).value y) x _| ≤ _
  rw [smooth_lineDeriv_mul (radialOutside 0 hu.le hu).regular
    (radialInside 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u)).regular]
  have hA : 0 < Real.pi*smoothTransitionBound := mul_pos Real.pi_pos smoothTransitionBound_pos
  have h1 := radialOutside_deriv_le 0 hu.le hu x a
  have h2 := radialInside_deriv_le 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u) x a
  have h3 := radialOutside_abs_le 0 hu.le hu x
  have h4 := radialInside_abs_le 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u) x
  apply (abs_add_le _ _).trans
  simp only [abs_mul]
  have hh1 := mul_le_mul h1 h4 (abs_nonneg _) (by positivity : 0 ≤ Real.pi*smoothTransitionBound/u)
  have hh2 := mul_le_mul h3 h2 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have hc : 0 ≤ Real.pi*smoothTransitionBound := by positivity
  have hd : Real.pi*smoothTransitionBound/(2*u) ≤ Real.pi*smoothTransitionBound/u :=
    div_le_div_of_nonneg_left hc hu (by linarith)
  calc
    _ ≤ Real.pi*smoothTransitionBound/u+Real.pi*smoothTransitionBound/(2*u) := by simpa only [mul_one,one_mul] using add_le_add hh1 hh2
    _ ≤ Real.pi*smoothTransitionBound/u+Real.pi*smoothTransitionBound/u := add_le_add_right hd _
    _ = _ := by ring

lemma shellCutoff_deriv_zero {u : ℝ} (hu : 0 < u) (x : Space)
    (hx : ‖x‖ < u) (a : Fin 3) :
    lineDeriv ℝ (shellCutoff hu).value x (spaceDirections a) = 0 := by
  have h1 : lineDeriv ℝ (radialOutside 0 hu.le hu).value x (spaceDirections a) = 0 := by
    change lineDeriv ℝ (fun z => Real.sin (radialPhase 0 u u z)) x _ = _
    rw [radial_sin_derivative,radialPhase_derivative_zero_off_collar hu.le hu (by simp only [sub_zero]; exact fun h => (not_le_of_gt hx) h.1),mul_zero]
  have h2 : (radialOutside 0 hu.le hu).value x = 0 := by
    exact (radialCut_inner hu.le hu (y := 0) (x := x) (by simpa using hx.le)).2
  change lineDeriv ℝ (fun y => (radialOutside 0 hu.le hu).value y*
    (radialInside 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u)).value y) x _ = _
  rw [smooth_lineDeriv_mul (radialOutside 0 hu.le hu).regular
    (radialInside 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u)).regular,h1,h2,zero_mul,zero_mul,add_zero]

lemma dyadic_shell_deriv_sum {r : ℝ} (hr : 0 < r) (K : ℕ) (x : Space) (a : Fin 3) :
    (∑ k ∈ Finset.range K,
      (lineDeriv ℝ (shellCutoff (mul_pos (pow_pos (by norm_num : (0:ℝ)<2) k) hr)).value x (spaceDirections a))^2) ≤
      (8*(Real.pi*smoothTransitionBound)^2/r^2)*(if r ≤ ‖x‖ then 1 else 0) := by
  classical
  by_cases hx : r ≤ ‖x‖
  · rw [ite_eq_left hx,mul_one]
    have hpoint (k : ℕ) :
        (lineDeriv ℝ (shellCutoff (mul_pos (pow_pos (by norm_num : (0:ℝ)<2) k) hr)).value x (spaceDirections a))^2 ≤
          (4*(Real.pi*smoothTransitionBound)^2/r^2)*(1/4:ℝ)^k := by
      have hh := pow_le_pow_left₀ (abs_nonneg _) (shellCutoff_deriv_le (mul_pos (pow_pos (by norm_num : (0:ℝ)<2) k) hr) x a) 2
      rw [sq_abs] at hh
      apply hh.trans_eq
      simp only [div_pow,mul_pow,one_div,inv_pow,←pow_mul]
      have hk : (2:ℝ)^(k*2) = 4^k := by rw [Nat.mul_comm,pow_mul]; norm_num
      rw [hk]
      ring
    have hg : (∑ k ∈ Finset.range K, (1/4:ℝ)^k) ≤ 2 := by
      have hh : (∑ k ∈ Finset.range K, (1/4:ℝ)^k) ≤ 2-2*(1/4:ℝ)^K := by
        induction K with
        | zero => norm_num
        | succ K ih =>
          rw [Finset.sum_range_succ,pow_succ]
          nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/4) K]
      nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/4) K]
    calc
      _ ≤ ∑ k ∈ Finset.range K, (4*(Real.pi*smoothTransitionBound)^2/r^2)*(1/4:ℝ)^k :=
        Finset.sum_le_sum fun k _ => hpoint k
      _ = (4*(Real.pi*smoothTransitionBound)^2/r^2)*(∑ k ∈ Finset.range K, (1/4:ℝ)^k) := (Finset.mul_sum ..).symm
      _ ≤ (4*(Real.pi*smoothTransitionBound)^2/r^2)*2 := mul_le_mul_of_nonneg_left hg (by positivity)
      _ = _ := by ring
  · rw [ite_eq_right hx,mul_zero]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro k hk
    rw [shellCutoff_deriv_zero _ x (lt_of_lt_of_le (lt_of_not_ge hx)
      (le_mul_of_one_le_left hr.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2)))) a,zero_pow (by decide : 2≠0)]
end CoulombAtom

end

end OAI
