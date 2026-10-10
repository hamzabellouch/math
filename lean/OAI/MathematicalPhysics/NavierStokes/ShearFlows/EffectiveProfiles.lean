import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Profiles

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology
namespace ShearFlows

def gluePower (k : ℕ) (x : ℝ) : ℝ := x⁻¹ ^ k * expNegInvGlue x

theorem gluePower_smooth (k : ℕ) : ContDiff ℝ ∞ (gluePower k) := by
  convert! (expNegInvGlue.contDiff_polynomial_eval_inv_mul (n := ⊤) (Polynomial.X ^ k)) using 1
  funext x
  simp only [gluePower, Polynomial.eval_pow, Polynomial.eval_X]

theorem gluePower_deriv (k : ℕ) (x : ℝ) :
    HasDerivAt (gluePower k)
      (gluePower (k+2) x - (k : ℝ) * gluePower (k+1) x) x := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (Polynomial.X ^ k) x
  simp only [Polynomial.derivative_X_pow, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at h
  convert! h using 1
  dsimp [gluePower]
  cases k <;> simp [pow_succ]
  ring

theorem gluePower_bound (k : ℕ) (x : ℝ) : |gluePower k x| ≤ (k.factorial : ℝ) := by
  by_cases hx : x ≤ 0
  · simp [gluePower, expNegInvGlue.zero_of_nonpos hx]
  have hxp : 0 < x := lt_of_not_ge hx
  have hy : 0 ≤ x⁻¹ := (inv_pos.mpr hxp).le
  have h := Real.pow_div_factorial_le_exp x⁻¹ hy k
  have he : 0 < Real.exp x⁻¹ := Real.exp_pos _
  have hf : (0 : ℝ) < k.factorial := by positivity
  rw [div_le_iff₀ hf] at h
  calc
    |gluePower k x| = x⁻¹ ^ k / Real.exp x⁻¹ := by
      simp [gluePower, expNegInvGlue, hx, Real.exp_neg, div_eq_mul_inv,
        abs_of_pos hxp]
    _ ≤ k.factorial := (div_le_iff₀ he).2 (by simpa [mul_comm] using h)

def transitionDen (x : ℝ) : ℝ := expNegInvGlue x + expNegInvGlue (1-x)

theorem transitionDen_ge (x : ℝ) : (1 / 9 : ℝ) ≤ transitionDen x := by
  have he : Real.exp (2 : ℝ) ≤ 9 := by
    have h := Real.exp_one_lt_three
    have hpos := Real.exp_pos (1 : ℝ)
    rw [show (2 : ℝ) = 1+1 by norm_num, Real.exp_add]
    nlinarith
  have hh : (1 / 9 : ℝ) ≤ expNegInvGlue (1/2) := by
    norm_num [expNegInvGlue, Real.exp_neg]
    simpa only [one_div] using (one_div_le_one_div_of_le (Real.exp_pos _) he)
  rcases le_total (1/2 : ℝ) x with hx | hx
  · exact hh.trans ((expNegInvGlue.monotone hx).trans
      (le_add_of_nonneg_right (expNegInvGlue.nonneg _)))
  · apply hh.trans
    calc
      expNegInvGlue (1/2) ≤ expNegInvGlue (1-x) :=
        expNegInvGlue.monotone (by linarith)
      _ ≤ transitionDen x := le_add_of_nonneg_left (expNegInvGlue.nonneg _)

def denomPower (k : ℕ) (x : ℝ) : ℝ := (transitionDen x)⁻¹ ^ k

theorem transitionDen_pos (x : ℝ) : 0 < transitionDen x :=
  (by norm_num : (0 : ℝ) < 1/9).trans_le (transitionDen_ge x)

theorem denomPower_smooth (k : ℕ) : ContDiff ℝ ∞ (denomPower k) := by
  exact ((expNegInvGlue.contDiff.add
    (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))).inv
      (fun x => (transitionDen_pos x).ne')).pow k

theorem transitionDen_deriv (x : ℝ) :
    HasDerivAt transitionDen (gluePower 2 x - gluePower 2 (1-x)) x := by
  have h0 (y : ℝ) : HasDerivAt expNegInvGlue (gluePower 2 y) y := by
    convert! gluePower_deriv 0 y using 1
    · funext x; simp [gluePower]
    · simp
  convert! (h0 x).add ((h0 (1-x)).comp x ((hasDerivAt_id x).const_sub 1)) using 1
  simp [sub_eq_add_neg]

theorem denomPower_deriv (k : ℕ) (x : ℝ) :
    HasDerivAt (denomPower k)
      (-(k : ℝ) * (gluePower 2 x - gluePower 2 (1-x)) * denomPower (k+1) x) x := by
  have h := ((transitionDen_deriv x).inv (transitionDen_pos x).ne').pow k
  convert! h using 1
  dsimp [denomPower]
  cases k with
  | zero => simp
  | succ k => simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one, pow_succ, div_eq_mul_inv, inv_pow]
              ring

theorem denomPower_bound (k : ℕ) (x : ℝ) : |denomPower k x| ≤ (9 : ℝ)^k := by
  have hb : (transitionDen x)⁻¹ ≤ 9 := by
    exact (inv_le_comm₀ (transitionDen_pos x) (by norm_num)).2
      (by simpa using transitionDen_ge x)
  simpa [denomPower, abs_of_pos (transitionDen_pos x)]
    using pow_le_pow_left₀ (inv_nonneg.mpr (transitionDen_pos x).le) hb k

inductive ProfileExpr
  | const (r : ℚ)
  | coord
  | glue (k : ℕ) (a b : ℚ)
  | denom (k : ℕ) (a b : ℚ)
  | add (f g : ProfileExpr)
  | mul (f g : ProfileExpr)
  deriving DecidableEq

namespace ProfileExpr

def val : ProfileExpr → ℝ → ℝ
  | .const r, _ => r
  | .coord, x => x
  | .glue k a b, x => gluePower k ((a : ℝ)*x+b)
  | .denom k a b, x => denomPower k ((a : ℝ)*x+b)
  | .add f g, x => f.val x + g.val x
  | .mul f g, x => f.val x * g.val x

def sub (f g : ProfileExpr) : ProfileExpr := .add f (.mul (.const (-1)) g)

def diff : ProfileExpr → ProfileExpr
  | .const _ => .const 0
  | .coord => .const 1
  | .glue k a b => .mul (.const a)
      (.sub (.glue (k+2) a b) (.mul (.const k) (.glue (k+1) a b)))
  | .denom k a b => .mul (.const (-a * k))
      (.mul (.sub (.glue 2 a b) (.glue 2 (-a) (1-b))) (.denom (k+1) a b))
  | .add f g => .add f.diff g.diff
  | .mul f g => .add (.mul f.diff g) (.mul f g.diff)

theorem smooth (e : ProfileExpr) : ContDiff ℝ ∞ e.val := by
  induction e with
  | const r => exact contDiff_const
  | coord => exact contDiff_id
  | glue k a b => exact (gluePower_smooth k).comp ((contDiff_const.mul contDiff_id).add contDiff_const)
  | denom k a b => exact (denomPower_smooth k).comp ((contDiff_const.mul contDiff_id).add contDiff_const)
  | add f g hf hg => exact hf.add hg
  | mul f g hf hg => exact hf.mul hg

theorem hasDerivAt (e : ProfileExpr) (x : ℝ) : HasDerivAt e.val (e.diff.val x) x := by
  induction e with
  | const r => simpa [diff, val] using hasDerivAt_const x (r : ℝ)
  | coord => convert! hasDerivAt_id x using 1; simp [diff, val]
  | glue k a b =>
    convert! (gluePower_deriv k ((a : ℝ)*x+b)).comp x
      (((hasDerivAt_id x).const_mul (a : ℝ)).add_const (b : ℝ)) using 1
    simp [diff, val, sub]
    ring
  | denom k a b =>
    convert! (denomPower_deriv k ((a : ℝ)*x+b)).comp x
      (((hasDerivAt_id x).const_mul (a : ℝ)).add_const (b : ℝ)) using 1
    simp only [diff, val, sub, Rat.cast_mul, Rat.cast_neg, Rat.cast_natCast, Rat.cast_sub, Rat.cast_one]
    rw [show -(a : ℝ) * x + (1 - b) = 1 - ((a : ℝ)*x+b) by ring]
    ring
  | add f g hf hg => exact hf.add hg
  | mul f g hf hg =>
    convert! hf.mul hg using 1

theorem val_diff (e : ProfileExpr) : e.diff.val = deriv e.val :=
  funext fun x => (hasDerivAt e x).deriv.symm

def diffN (e : ProfileExpr) : ℕ → ProfileExpr
  | 0 => e
  | n+1 => (e.diffN n).diff

theorem val_diffN (e : ProfileExpr) (n : ℕ) : (e.diffN n).val = iteratedDeriv n e.val := by
  induction n with
  | zero => rfl
  | succ n h => simpa [diffN, val_diff, iteratedDeriv_succ] using congrArg deriv h

def bound (M : ℚ) : ProfileExpr → ℚ
  | .const r => |r|
  | .coord => |M|
  | .glue k _ _ => k.factorial
  | .denom k _ _ => 9^k
  | .add f g => f.bound M + g.bound M
  | .mul f g => f.bound M * g.bound M

theorem bound_nonneg (e : ProfileExpr) (M : ℚ) : 0 ≤ e.bound M := by
  induction e <;> simp only [bound] <;> positivity

theorem val_bound (e : ProfileExpr) {M : ℚ} {x : ℝ} (hx : |x| ≤ |(M : ℝ)|) :
    |e.val x| ≤ (e.bound M : ℝ) := by
  induction e with
  | const r => simp [val, bound]
  | coord => simpa [val, bound] using hx
  | glue k a b => simpa [val, bound] using gluePower_bound k ((a : ℝ)*x+b)
  | denom k a b => simpa [val, bound] using denomPower_bound k ((a : ℝ)*x+b)
  | add f g hf hg => simpa [val, bound] using (abs_add_le (f.val x) (g.val x)).trans (add_le_add hf hg)
  | mul f g hf hg =>
    have h := mul_le_mul hf hg (abs_nonneg (g.val x))
      (show (0 : ℝ) ≤ f.bound M by exact_mod_cast bound_nonneg f M)
    simpa [val, bound, abs_mul] using h

def transition (a b : ℚ) : ProfileExpr := .mul (.glue 0 a b) (.denom 1 a b)
def ramp (a b : ℚ) : ProfileExpr := transition (b-a)⁻¹ (-a/(b-a))
def cutoff (a b c d : ℚ) : ProfileExpr :=
  .mul (ramp a b) (transition (-(d-c)⁻¹) (d/(d-c)))
def potential (a b c d p : ℚ) : ProfileExpr :=
  .mul (.sub .coord (.const p)) (cutoff a b c d)

theorem val_transition (a b : ℚ) (x : ℝ) :
    (transition a b).val x = Real.smoothTransition ((a : ℝ)*x+b) := by
  simp [transition, val, gluePower, denomPower, transitionDen, Real.smoothTransition, div_eq_mul_inv]

theorem val_ramp (a b : ℚ) : (ramp a b).val = smoothRamp a b := by
  funext x
  rw [ramp, val_transition]
  dsimp [smoothRamp]
  congr 1
  push_cast
  ring

theorem val_cutoff (a b c d : ℚ) : (cutoff a b c d).val = closedCutoff a b c d := by
  funext x
  simp only [cutoff, val, val_ramp, val_transition, closedCutoff, smoothRamp]
  congr 2
  push_cast
  simp only [sub_neg_eq_add, neg_add_eq_sub]
  ring

theorem val_potential (a b c d p : ℚ) :
    (potential a b c d p).val = fun x => (x-(p : ℝ)) * closedCutoff a b c d x := by
  simp only [potential, val, sub, val_cutoff]
  funext x
  push_cast
  ring

end ProfileExpr
end ShearFlows

end

end OAI
