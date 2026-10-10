import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorOutgoing
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Star

namespace OAI

/-! # A concrete differential algebra for the exterior radial ODE

Every time derivative of the bounded exterior state is a finite expression
in its two components, their conjugates, and `exp(2t)`.  This syntax records
that elementary fact without expanding large higher derivatives.
-/

open Filter Set Topology

namespace DefocusingNLS

inductive RadialODEExpr where
  | constant : ℂ → RadialODEExpr
  | exponential : RadialODEExpr
  | position : RadialODEExpr
  | velocity : RadialODEExpr
  | add : RadialODEExpr → RadialODEExpr → RadialODEExpr
  | mul : RadialODEExpr → RadialODEExpr → RadialODEExpr
  | conjugate : RadialODEExpr → RadialODEExpr

namespace RadialODEExpr

noncomputable def eval (f g : ℝ → ℂ) (t : ℝ) : RadialODEExpr → ℂ
  | constant c => c
  | exponential => (Real.exp (2 * t) : ℂ)
  | position => f t
  | velocity => g t
  | add a b => eval f g t a + eval f g t b
  | mul a b => eval f g t a * eval f g t b
  | conjugate a => star (eval f g t a)

def pow (a : RadialODEExpr) : ℕ → RadialODEExpr
  | 0 => constant 1
  | n + 1 => mul (pow a n) a

theorem eval_pow (f g : ℝ → ℂ) (t : ℝ) (a : RadialODEExpr) (n : ℕ) :
    eval f g t (pow a n) = eval f g t a ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow, eval, ih, pow_succ]

noncomputable def acceleration (ν : ℂ) (n : ℕ) : RadialODEExpr :=
  add (add (mul (constant (-(2 * ν + 10))) velocity)
      (mul (mul (constant (-Complex.I / 2)) exponential) velocity))
    (add (mul (constant (-(ν * (ν + 10)))) position)
      (mul (pow position (n + 1)) (pow (conjugate position) n)))

theorem eval_acceleration (ν : ℂ) (n : ℕ) (f g : ℝ → ℂ) (t : ℝ) :
    eval f g t (acceleration ν n) =
      -(2 * ν + 10 + Complex.I * (Real.exp (2 * t) / 2 : ℝ)) * g t -
        ν * (ν + 10) * f t + oddPowerNonlinearity n (f t) := by
  simp only [acceleration, eval, eval_pow, oddPowerNonlinearity, Complex.ofReal_div,
    Complex.ofReal_ofNat]
  ring

noncomputable def differentiate (ν : ℂ) (n : ℕ) : RadialODEExpr → RadialODEExpr
  | constant _ => constant 0
  | exponential => mul (constant 2) exponential
  | position => velocity
  | velocity => acceleration ν n
  | add a b => add (differentiate ν n a) (differentiate ν n b)
  | mul a b => add (mul (differentiate ν n a) b) (mul a (differentiate ν n b))
  | conjugate a => conjugate (differentiate ν n a)

theorem hasDerivAt_eval (ν : ℂ) (n : ℕ) (f g : ℝ → ℂ) (t : ℝ)
    (hf : HasDerivAt f (g t) t)
    (hg : HasDerivAt g (eval f g t (acceleration ν n)) t) (a : RadialODEExpr) :
    HasDerivAt (fun s => eval f g s a) (eval f g t (differentiate ν n a)) t := by
  induction a with
  | constant c => exact hasDerivAt_const t c
  | exponential =>
      convert (((hasDerivAt_id t).const_mul 2).exp).ofReal_comp using 1 <;>
        simp only [eval, differentiate, Complex.ofReal_mul, Complex.ofReal_ofNat, id_eq, mul_one]
      ring
  | position => exact hf
  | velocity => exact hg
  | add a b ha hb => exact ha.add hb
  | mul a b ha hb => exact ha.mul hb
  | conjugate a ha => exact ha.star

theorem iteratedDeriv_position (ν : ℂ) (n : ℕ) (f g : ℝ → ℂ) (L : ℝ)
    (hf : ∀ t, L < t → HasDerivAt f (g t) t)
    (hg : ∀ t, L < t → HasDerivAt g (eval f g t (acceleration ν n)) t)
    (k : ℕ) : ∀ t, L < t →
      iteratedDeriv k f t = eval f g t ((differentiate ν n)^[k] position) := by
  induction k with
  | zero =>
      intro t ht
      simp only [iteratedDeriv_zero, Function.iterate_zero, id_eq, eval]
  | succ k ih =>
      intro t ht
      have he : iteratedDeriv k f =ᶠ[𝓝 t]
          (fun s => eval f g s ((differentiate ν n)^[k] position)) := by
        filter_upwards [eventually_gt_nhds ht] with s hs
        exact ih s hs
      rw [iteratedDeriv_succ, he.deriv_eq]
      simpa only [Function.iterate_succ_apply'] using
        (hasDerivAt_eval ν n f g t (hf t ht) (hg t ht)
          ((differentiate ν n)^[k] position)).deriv

end RadialODEExpr

end DefocusingNLS

end OAI
