import Mathlib

namespace OAI

open Matrix

namespace CurrentKS.Difference
open Set
open scoped ContDiff

theorem quadratic_remainder {f : ℝ → ℝ} {h M : ℝ} (hh : 0 < h)
    (hf : ContDiffOn ℝ 3 f (Icc 0 h)) (hf0 : ContDiffAt ℝ 3 f 0)
    (hM : ∀ t ∈ Ioo 0 h, |iteratedDeriv 3 f t| ≤ M) :
    |f h - (f 0 + h * iteratedDeriv 1 f 0 + h^2/2 * iteratedDeriv 2 f 0)| ≤ M*h^3/6 := by
  obtain ⟨t,ht,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n:=2) (ne_of_lt hh)
    (by norm_num only [Nat.cast_ofNat, Set.uIcc_of_le hh.le]; exact hf)
  simp only [Set.uIoo_of_le hh.le, Set.uIcc_of_le hh.le] at ht he
  have h1 := iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hh)
    (hf0.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)) (left_mem_Icc.mpr hh.le)
  have h2 := iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hh)
    (hf0.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) (left_mem_Icc.mpr hh.le)
  have heval : taylorWithinEval f 2 (Icc 0 h) 0 h =
      f 0 + h * iteratedDeriv 1 f 0 + h^2/2 * iteratedDeriv 2 f 0 := by
    rw [show 2=1+1 from rfl,taylorWithinEval_succ,taylorWithinEval_succ,
      taylor_within_zero_eval]
    norm_num only [Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat, zero_add, one_mul, inv_one,sub_zero,pow_one,smul_eq_mul]
    rw [h1,h2]
    ring
  rw [heval] at he
  rw [he]
  norm_num only [Nat.factorial, Nat.cast_ofNat, sub_zero, abs_div, abs_mul,
    abs_pow, abs_of_pos hh]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hM t ht) (by positivity)) (by norm_num)

theorem gradient_error {fp fm f0 g H h M e vp vm : ℝ}
    (hh : 0 < h) (_he : 0 ≤ e)
    (hp : |fp-(f0+h*g+h^2/2*H)| ≤ M*h^3/6)
    (hm : |fm-(f0-h*g+h^2/2*H)| ≤ M*h^3/6)
    (hvp : |vp-fp| ≤ e) (hvm : |vm-fm| ≤ e) :
    |(vp-vm)/(2*h)-g| ≤ M*h^2/6+e/h := by
  have ha : |(vp-vm)-2*h*g| ≤ M*h^3/3+2*e := by
    have H1 := abs_add_le (vp-fp) (fp-(f0+h*g+h^2/2*H))
    have H2 := abs_add_le ((vp-fp)+(fp-(f0+h*g+h^2/2*H)))
      (-(vm-fm)-(fm-(f0-h*g+h^2/2*H)))
    have H3 := abs_sub (-(vm-fm)) (fm-(f0-h*g+h^2/2*H))
    rw [abs_neg] at H3
    have : (vp-fp)+(fp-(f0+h*g+h^2/2*H))+
        (-(vm-fm)-(fm-(f0-h*g+h^2/2*H))) = (vp-vm)-2*h*g := by ring
    rw [this] at H2
    linarith
  have heq : (vp-vm)/(2*h)-g = ((vp-vm)-2*h*g)/(2*h) := by field_simp
  rw [heq,abs_div,abs_of_pos (mul_pos (by norm_num) hh)]
  apply (div_le_iff₀ (mul_pos (by norm_num) hh)).mpr
  calc
    |vp-vm-2*h*g| ≤ M*h^3/3+2*e := ha
    _ = (M*h^2/6+e/h)*(2*h) := by field_simp; ring

theorem diagonal_error {fp fm f0 g H h M e vp vm v0 : ℝ}
    (hh : 0 < h) (_he : 0 ≤ e)
    (hp : |fp-(f0+h*g+h^2/2*H)| ≤ M*h^3/6)
    (hm : |fm-(f0-h*g+h^2/2*H)| ≤ M*h^3/6)
    (hvp : |vp-fp| ≤ e) (hvm : |vm-fm| ≤ e) (hv0 : |v0-f0| ≤ e) :
    |(vp-2*v0+vm)/h^2-H| ≤ M*h/3+4*e/h^2 := by
  have hp' := abs_le.mp hp
  have hm' := abs_le.mp hm
  have hvp' := abs_le.mp hvp
  have hvm' := abs_le.mp hvm
  have hv0' := abs_le.mp hv0
  have ha : |vp-2*v0+vm-h^2*H| ≤ M*h^3/3+4*e := by
    rw [abs_le]
    constructor <;> linarith
  have heq : (vp-2*v0+vm)/h^2-H = (vp-2*v0+vm-h^2*H)/h^2 := by field_simp
  rw [heq,abs_div,abs_of_pos (sq_pos_of_pos hh)]
  apply (div_le_iff₀ (sq_pos_of_pos hh)).mpr
  calc
    |vp-2*v0+vm-h^2*H| ≤ M*h^3/3+4*e := ha
    _ = (M*h/3+4*e/h^2)*h^2 := by field_simp

end CurrentKS.Difference

end OAI
