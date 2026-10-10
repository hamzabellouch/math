import OAI.Analysis.LipschitzHilbert.Estimates.PolynomialEnvelope
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv

namespace OAI

/-! Fixed polynomial weights preserve the required packet decay and
horizontal derivative bounds, after choosing the original packet order. -/

noncomputable section

namespace LipschitzHilbert

theorem polynomialWeight_derivative (a r x : ℝ) (q : ℕ) (hr : 0 < r) :
    |deriv (polynomialWeight a r q) x| ≤
      (2*(q:ℝ)/r)*polynomialWeight a r q x := by
  cases q with
  | zero =>
    change |deriv (fun _ : ℝ => (1:ℝ)) x| ≤ _
    simp
  | succ q =>
    let t := (x-a)/r
    let B := 1+t^2
    have hB : 0 < B := by dsimp [B]; positivity
    have ht : |t| ≤ B := by dsimp [B]; nlinarith [sq_nonneg (|t|-1), sq_abs t]
    have hd := ((((hasDerivAt_id x).sub_const a).div_const r).pow 2).const_add 1 |>.pow (q+1)
    dsimp only [Pi.pow_apply, id_eq] at hd
    change HasDerivAt (fun y : ℝ => (1+((y-a)/r)^2)^(q+1)) _ x at hd
    have heq : (fun y : ℝ => (1+((y-a)/r)^2)^(q+1)) = polynomialWeight a r (q+1) := by
      funext y
      simp only [polynomialWeight, div_pow]
    rw [heq] at hd
    rw [hd.deriv]
    have habs : |(q+1:ℝ) * B^q * (2*t*(1/r))| =
        (2*(q+1:ℝ)/r)*B^q*|t| := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (q+1:ℝ)),
        abs_of_nonneg (pow_nonneg hB.le q), abs_of_pos (by norm_num : (0:ℝ)<2),
        abs_of_pos (by positivity : 0 < 1/r)]
      ring
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, Nat.cast_ofNat] at *
    simp only [Nat.reduceSub, pow_one, polynomialWeight, ← div_pow]
    change |(q+1:ℝ)*B^q*(2*t*(1/r))| ≤ (2*(q+1:ℝ)/r)*B^(q+1)
    rw [habs, pow_succ]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ht
      (show 0 ≤ (2*(q+1:ℝ)/r)*B^q by positivity)

theorem polynomialWeight_mul_envelope (x s a l r : ℝ) (q n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r) (hsa : |s-a| ≤ r) :
    polynomialWeight a r q x * lineEnvelope s l (n+2*q) x ≤
      16^q * lineEnvelope s l n x := by
  have hP := polynomialWeight_one_le a r q x
  have hsq : polynomialWeight a r q x ≤ polynomialWeight a r q x^2 := by nlinarith
  exact (mul_le_mul_of_nonneg_right hsq (lineEnvelope_nonneg _ _ _ _)).trans
    (polynomialWeight_sq_mul_envelope x s a l r q n hl hr hlr hsa)

theorem polynomialLocalization_packet_bound (f : SchwartzMap ℝ ℂ)
    (a r s l C : ℝ) (q n : ℕ) (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r)
    (hsa : |s-a| ≤ r) (hC : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C*lineEnvelope s l (n+2*q) x) (x : ℝ) :
    ‖polynomialLocalization a r q f x‖ ≤ (16^q*C)*lineEnvelope s l n x := by
  rw [polynomialLocalization_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ((polynomialWeight_one_le a r q x).trans' (by norm_num))]
  calc
    _ ≤ polynomialWeight a r q x * (C*lineEnvelope s l (n+2*q) x) :=
      mul_le_mul_of_nonneg_left (hf x) (zero_le_one.trans (polynomialWeight_one_le a r q x))
    _ = C*(polynomialWeight a r q x * lineEnvelope s l (n+2*q) x) := by ring
    _ ≤ C*(16^q*lineEnvelope s l n x) := mul_le_mul_of_nonneg_left
      (polynomialWeight_mul_envelope x s a l r q n hl hr hlr hsa) hC
    _ = _ := by ring

theorem polynomialWeight_differentiable (a r : ℝ) (q : ℕ) :
    Differentiable ℝ (polynomialWeight a r q) := by
  unfold polynomialWeight
  fun_prop

theorem polynomialLocalization_deriv (f : SchwartzMap ℝ ℂ) (a r : ℝ) (q : ℕ) (x : ℝ) :
    deriv (polynomialLocalization a r q f) x =
      ((deriv (polynomialWeight a r q) x : ℝ) : ℂ)*f x +
        (polynomialWeight a r q x : ℂ)*deriv f x := by
  have hd := (((polynomialWeight_differentiable a r q) x).hasDerivAt.ofReal_comp).mul
    ((f.differentiable x).hasDerivAt)
  have heq : (fun y => (polynomialWeight a r q y : ℂ)*f y) =
      polynomialLocalization a r q f := by
    funext y
    exact (polynomialLocalization_apply a r q f y).symm
  change HasDerivAt (fun y => (polynomialWeight a r q y : ℂ)*f y) _ x at hd
  rw [heq] at hd
  exact hd.deriv

theorem polynomialLocalization_derivative_bound (f : SchwartzMap ℝ ℂ)
    (a r s l C : ℝ) (q n : ℕ) (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r)
    (hsa : |s-a| ≤ r) (hC : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C*lineEnvelope s l (n+2*q) x)
    (hdf : ∀ x, ‖deriv f x‖ ≤ (C/l)*lineEnvelope s l (n+2*q) x) (x : ℝ) :
    ‖deriv (polynomialLocalization a r q f) x‖ ≤
      ((16^q*(1+2*(q:ℝ))*C)/l)*lineEnvelope s l n x := by
  rw [polynomialLocalization_deriv]
  have hP : 0 ≤ polynomialWeight a r q x :=
    zero_le_one.trans (polynomialWeight_one_le a r q x)
  have hq : 0 ≤ 2*(q:ℝ) := by positivity
  have hradius : 2*(q:ℝ)/r ≤ 2*(q:ℝ)/l :=
    div_le_div_of_nonneg_left hq hl hlr
  have hw := (polynomialWeight_derivative a r x q hr).trans
    (mul_le_mul_of_nonneg_right hradius hP)
  calc
    _ ≤ ‖((deriv (polynomialWeight a r q) x : ℝ) : ℂ)*f x‖ +
        ‖(polynomialWeight a r q x : ℂ)*deriv f x‖ := norm_add_le _ _
    _ = |deriv (polynomialWeight a r q) x| * ‖f x‖ +
        polynomialWeight a r q x * ‖deriv f x‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hP]
    _ ≤ ((2*(q:ℝ)/l)*polynomialWeight a r q x) *
        (C*lineEnvelope s l (n+2*q) x) + polynomialWeight a r q x *
        ((C/l)*lineEnvelope s l (n+2*q) x) :=
      add_le_add (mul_le_mul hw (hf x) (norm_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_left (hdf x) hP)
    _ = ((1+2*(q:ℝ))*C/l) *
        (polynomialWeight a r q x * lineEnvelope s l (n+2*q) x) := by ring
    _ ≤ ((1+2*(q:ℝ))*C/l) * (16^q*lineEnvelope s l n x) :=
      mul_le_mul_of_nonneg_left (polynomialWeight_mul_envelope x s a l r q n hl hr hlr hsa)
        (by positivity)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
