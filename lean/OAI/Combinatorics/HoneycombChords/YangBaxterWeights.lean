import OAI.Combinatorics.HoneycombChords.YangBaxterDefinitions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Algebra.BigOperators.Field

namespace OAI

/-! Sine parametrization and phase normalization of the honeycomb transfer weights.

The formulas follow the finite strip transfer calculation in the companion paper
on uniform marked polygon estimates. -/

namespace CriticalHoneycomb.Transfer.YangBaxter
open scoped BigOperators

noncomputable def angle : ℝ := Real.pi/8
noncomputable def sine2 : ℝ := Real.sin (2*angle)

lemma cos_two_angle : Real.cos (2*angle) = sine2 := by
  unfold sine2
  rw [show 2*angle = Real.pi/4 by unfold angle; ring,
    Real.cos_pi_div_four, Real.sin_pi_div_four]

lemma sine2_sq : sine2^2 = (1:ℝ)/2 := by
  have h := Real.sin_sq_add_cos_sq (2*angle)
  rw [cos_two_angle] at h
  change sine2^2+sine2^2=1 at h
  linarith

lemma sin_angle_sq : (Real.sin angle)^2 = (1-sine2)/2 := by
  have h := Real.cos_two_mul angle
  rw [cos_two_angle] at h
  nlinarith only [h, Real.sin_sq_add_cos_sq angle]

lemma cos_angle_eq : Real.cos angle = (2*sine2+1)*Real.sin angle := by
  have h : Real.sin angle = sine2*(Real.cos angle-Real.sin angle) := by
    calc
      Real.sin angle = Real.cos (3*angle) := by
        rw [show 3*angle=Real.pi/2-angle by unfold angle; ring, Real.cos_pi_div_two_sub]
      _ = sine2*(Real.cos angle-Real.sin angle) := by
        rw [show 3*angle=2*angle+angle by ring, Real.cos_add, cos_two_angle]
        unfold sine2
        ring
  linear_combination -2*sine2*h - 2*(Real.cos angle-Real.sin angle)*sine2_sq

lemma trig_constraints (u v : ℝ) :
    (Real.cos angle : ℂ) = (2*(sine2:ℂ)+1)*(Real.sin angle:ℂ) ∧
    (Real.sin angle : ℂ)^2 = (1-(sine2:ℂ))/2 ∧
    (sine2 : ℂ)^2 = 1/2 ∧
    (Real.cos u : ℂ)^2 + (Real.sin u : ℂ)^2 = 1 ∧
    (Real.cos v : ℂ)^2 + (Real.sin v : ℂ)^2 = 1 ∧
    Complex.I^2+1=0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, by simp⟩
  · exact_mod_cast cos_angle_eq
  · exact_mod_cast sin_angle_sq
  · have h := congrArg Complex.ofReal sine2_sq
    push_cast at h
    exact h
  · exact_mod_cast Real.cos_sq_add_sin_sq u
  · exact_mod_cast Real.cos_sq_add_sin_sq v

noncomputable def denominator (u : ℝ) : ℂ :=
  (Real.sin (2*angle+u) * Real.sin (3*angle+u) : ℝ)
noncomputable def phase : ℂ := Complex.exp ((2*angle : ℝ) * Complex.I)

lemma sin_three_angle : Real.sin (3*angle)=Real.cos angle := by
  rw [show 3*angle = Real.pi/2-angle by unfold angle; ring, Real.sin_pi_div_two_sub]
lemma cos_three_angle : Real.cos (3*angle)=Real.sin angle := by
  rw [show 3*angle = Real.pi/2-angle by unfold angle; ring, Real.cos_pi_div_two_sub]

lemma denominator_eq (u : ℝ) : denominator u =
    (sine2:ℂ)*((Real.cos u:ℂ)+(Real.sin u:ℂ))*
      ((Real.cos angle:ℂ)*(Real.cos u:ℂ)+(Real.sin angle:ℂ)*(Real.sin u:ℂ)) := by
  unfold denominator
  rw [Real.sin_add, Real.sin_add, cos_two_angle, sin_three_angle, cos_three_angle]
  simp only [Complex.ofReal_mul, Complex.ofReal_add]
  change ((sine2:ℂ)*(Real.cos u:ℂ)+(sine2:ℂ)*(Real.sin u:ℂ))*
    ((Real.cos angle:ℂ)*(Real.cos u:ℂ)+(Real.sin angle:ℂ)*(Real.sin u:ℂ)) = _
  ring

lemma phase_eq : phase = (sine2:ℂ)*(1+Complex.I) := by
  unfold phase
  rw [Complex.exp_ofReal_mul_I, cos_two_angle]
  change (sine2:ℂ)+(sine2:ℂ)*Complex.I=_
  ring

lemma phase_sq : phase^2 = Complex.I := by
  unfold phase
  rw [← Complex.exp_nat_mul]
  convert Complex.exp_pi_div_two_mul_I using 1
  push_cast
  unfold angle
  push_cast
  ring_nf

lemma phase_ne_zero : phase ≠ 0 := Complex.exp_ne_zero _

lemma phase_inverse : phase⁻¹ = (sine2:ℂ)*(1-Complex.I) := by
  apply mul_left_cancel₀ phase_ne_zero
  rw [mul_inv_cancel₀ phase_ne_zero, phase_eq]
  have hs := (trig_constraints 0 0).2.2.1
  have hi : Complex.I^2+1=0 := by simp
  linear_combination -2*hs + (sine2:ℂ)^2*hi

noncomputable def sourceR (u : ℝ) (p q : Fin 3 × Fin 3) : ℂ :=
  let a := (sine2 * Real.sin (3*angle-u) : ℝ) / denominator u
  let h := (sine2 * Real.sin u : ℝ) / denominator u
  let v := (Real.sin (3*angle-u) * Real.sin u : ℝ) / denominator u
  let c := (Real.sin (3*angle-u) * Real.sin (2*angle-u) : ℝ) / denominator u
  let d := (Real.sin u * Real.sin (u-angle) : ℝ) / denominator u
  match p.1.val, p.2.val, q.1.val, q.2.val with
  | 0, 0, 0, 0 => c
  | 2, 2, 2, 2 => c
  | 0, 1, 0, 1 => v
  | 1, 0, 1, 0 => v
  | 2, 1, 2, 1 => v
  | 1, 2, 1, 2 => v
  | 0, 1, 1, 0 => a
  | 1, 0, 0, 1 => a
  | 2, 1, 1, 2 => a
  | 1, 2, 2, 1 => a
  | 0, 2, 0, 2 => d
  | 0, 2, 1, 1 => h/phase
  | 0, 2, 2, 0 => c+d/phase^2
  | 1, 1, 0, 2 => h*phase
  | 1, 1, 1, 1 => 1
  | 1, 1, 2, 0 => h/phase
  | 2, 0, 0, 2 => c+d*phase^2
  | 2, 0, 1, 1 => h*phase
  | 2, 0, 2, 0 => d
  | _, _, _, _ => 0

lemma h_plus (x q : ℂ) : ((sine2:ℂ)*x/q)*phase=(x/2*(1+Complex.I))/q := by
  rw [phase_eq]
  have hs : (sine2:ℂ)^2=1/2 := (trig_constraints 0 0).2.2.1
  simp only [div_eq_mul_inv]
  linear_combination x*(1+Complex.I)*q⁻¹*hs

lemma h_minus (x q : ℂ) : ((sine2:ℂ)*x/q)/phase=(x/2*(1-Complex.I))/q := by
  simp only [div_eq_mul_inv, phase_inverse]
  have hs : (sine2:ℂ)^2=1/2 := (trig_constraints 0 0).2.2.1
  linear_combination x*(1-Complex.I)*q⁻¹*hs

lemma c_minus (c d q : ℂ) : c/q+(d/q)/phase^2=(c-Complex.I*d)/q := by
  rw [phase_sq]
  simp only [div_eq_mul_inv, Complex.inv_I]
  ring

lemma c_plus (c d q : ℂ) : c/q+(d/q)*phase^2=(c+Complex.I*d)/q := by
  rw [phase_sq]
  ring

lemma sourceR_eq_numerator (u : ℝ) (hd : denominator u ≠ 0)
    (p q : Fin 3 × Fin 3) :
    sourceR u p q = numerator (Real.cos angle) (Real.sin angle) sine2
      (Real.sin u) (Real.cos u) Complex.I p q / denominator u := by
  dsimp only [sourceR, numerator]
  split
  all_goals try simp_all only [Real.sin_sub, sin_three_angle, cos_three_angle, cos_two_angle,
    Complex.ofReal_mul, Complex.ofReal_sub, h_plus, h_minus, c_minus, c_plus]
  all_goals try (rw [← denominator_eq, div_self hd])
  all_goals try dsimp only [sine2]
  all_goals first | rfl | ring

lemma physical_left_sum (u v : ℝ)
    (hu : denominator u ≠ 0) (hv : denominator v ≠ 0)
    (hd : denominator (u-v) ≠ 0) (a b c d e f : Fin 3) :
    (∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      sourceR (u-v) (a,b) (j,k) * sourceR u (j,c) (d,l) *
      sourceR v (k,l) (e,f)) =
    leftComponent (Real.cos angle) (Real.sin angle) sine2
      (Real.sin u) (Real.cos u) (Real.sin v) (Real.cos v) Complex.I
      a b c d e f / (denominator (u-v) * denominator u * denominator v) := by
  simp only [leftComponent, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [sourceR_eq_numerator _ hd, sourceR_eq_numerator _ hu,
    sourceR_eq_numerator _ hv]
  simp only [Real.sin_sub, Real.cos_sub, Complex.ofReal_sub,
    Complex.ofReal_add, Complex.ofReal_mul]
  ring

lemma physical_right_sum (u v : ℝ)
    (hu : denominator u ≠ 0) (hv : denominator v ≠ 0)
    (hd : denominator (u-v) ≠ 0) (a b c d e f : Fin 3) :
    (∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      sourceR v (b,c) (k,l) * sourceR u (a,l) (j,f) *
      sourceR (u-v) (j,k) (d,e)) =
    rightComponent (Real.cos angle) (Real.sin angle) sine2
      (Real.sin u) (Real.cos u) (Real.sin v) (Real.cos v) Complex.I
      a b c d e f / (denominator (u-v) * denominator u * denominator v) := by
  simp only [rightComponent, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [sourceR_eq_numerator _ hv, sourceR_eq_numerator _ hu,
    sourceR_eq_numerator _ hd]
  simp only [Real.sin_sub, Real.cos_sub, Complex.ofReal_sub,
    Complex.ofReal_add, Complex.ofReal_mul]
  ring

end CriticalHoneycomb.Transfer.YangBaxter

end OAI
