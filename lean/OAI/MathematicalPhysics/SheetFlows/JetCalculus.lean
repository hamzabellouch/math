import Mathlib
import OAI.MathematicalPhysics.SheetFlows.Model

namespace OAI

/-! SheetFlows jet calculus. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology Polynomial
namespace Solenoidal

def flatJet (p : ℚ[X]) (x : ℝ) : ℝ :=
  (p.map (Rat.castHom ℝ)).eval x⁻¹ * expNegInvGlue x

def flatNext (p : ℚ[X]) : ℚ[X] := Polynomial.X ^ 2 * (p - p.derivative)

theorem flatJet_smooth (p : ℚ[X]) : ContDiff ℝ (⊤ : ℕ∞) (flatJet p) :=
  expNegInvGlue.contDiff_polynomial_eval_inv_mul _

theorem flatJet_hasDerivAt (p : ℚ[X]) (x : ℝ) :
    HasDerivAt (flatJet p) (flatJet (flatNext p) x) x := by
  unfold flatJet
  simpa only [flatNext, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.derivative_map] using
    expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (p.map (Rat.castHom ℝ)) x

def flatBound (p : ℚ[X]) : ℚ := ∑ n ∈ p.support, |p.coeff n| * n.factorial

theorem flatBound_nonneg (p : ℚ[X]) : 0 ≤ flatBound p := by
  apply Finset.sum_nonneg
  intro n _
  positivity

theorem pow_mul_exp_neg_le_factorial {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    z^n * Real.exp (-z) ≤ n.factorial := by
  have h := Real.pow_div_factorial_le_exp z hz n
  have hf : (0:ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hh : z^n ≤ (n.factorial:ℝ)*Real.exp z := by
    simpa [mul_comm] using (div_le_iff₀ hf).mp h
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  exact hh

theorem flatJet_bound (p : ℚ[X]) (x : ℝ) : |flatJet p x| ≤ (flatBound p : ℝ) := by
  by_cases hx : x ≤ 0
  · simp only [flatJet, expNegInvGlue.zero_of_nonpos hx, mul_zero, abs_zero]
    exact_mod_cast flatBound_nonneg p
  have hx : 0 < x := lt_of_not_ge hx
  have hi : 0 ≤ x⁻¹ := inv_nonneg.mpr hx.le
  have he : expNegInvGlue x = Real.exp (-x⁻¹) := by simp [expNegInvGlue,hx.not_ge]
  have hv : (p.map (Rat.castHom ℝ)).eval x⁻¹ =
      ∑ n ∈ p.support, (p.coeff n : ℝ) * (x⁻¹)^n := by
    rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum]
    rfl
  rw [flatJet, hv, he, Finset.sum_mul]
  calc
    |∑ n ∈ p.support, (p.coeff n:ℝ)*(x⁻¹)^n*Real.exp (-x⁻¹)|
        ≤ ∑ n ∈ p.support, |(p.coeff n:ℝ)*(x⁻¹)^n*Real.exp (-x⁻¹)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ p.support, (|p.coeff n|:ℝ)*(n.factorial:ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hi _), abs_of_pos (Real.exp_pos _)]
      simpa only [Rat.cast_abs, Nat.cast_ofNat, mul_assoc] using
        mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le_factorial hi n) (abs_nonneg (p.coeff n:ℝ))
    _ = (flatBound p:ℝ) := by simp [flatBound]

def transitionReciprocal (x : ℝ) : ℝ :=
  (expNegInvGlue x + expNegInvGlue (1-x))⁻¹

theorem transitionReciprocal_smooth : ContDiff ℝ (⊤ : ℕ∞) transitionReciprocal := by
  exact (expNegInvGlue.contDiff.add
    (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))).inv
      (fun x => (Real.smoothTransition.pos_denom x).ne')

theorem transitionReciprocal_bound (x : ℝ) : |transitionReciprocal x| ≤ 16 := by
  have hhalf : expNegInvGlue (1/2) = Real.exp (-2) := by norm_num [expNegInvGlue]
  have hlow : Real.exp (-2) ≤ expNegInvGlue x + expNegInvGlue (1-x) := by
    rw [← hhalf]
    rcases le_or_gt (1/2:ℝ) x with hx | hx
    · exact (expNegInvGlue.monotone hx).trans (le_add_of_nonneg_right (expNegInvGlue.nonneg _))
    · exact (expNegInvGlue.monotone (by linarith : (1/2:ℝ) ≤ 1-x)).trans
        (le_add_of_nonneg_left (expNegInvGlue.nonneg _))
  have hpos := Real.smoothTransition.pos_denom x
  have hb : (expNegInvGlue x + expNegInvGlue (1-x))⁻¹ ≤ Real.exp 2 := by
    calc
      _ ≤ (Real.exp (-2))⁻¹ := inv_anti₀ (Real.exp_pos _) hlow
      _ = Real.exp 2 := by rw [Real.exp_neg, inv_inv]
  have he : Real.exp (2:ℝ) < 9 := by
    have he := Real.exp_one_lt_three
    have hp := Real.exp_pos (1:ℝ)
    rw [show (2:ℝ) = 1+1 by norm_num, Real.exp_add]
    nlinarith
  rw [transitionReciprocal, abs_of_pos (inv_pos.mpr hpos)]
  linarith

theorem transitionReciprocal_hasDerivAt (x : ℝ) :
    HasDerivAt transitionReciprocal
      (-(transitionReciprocal x * transitionReciprocal x) *
        (flatJet (Polynomial.X^2) x - flatJet (Polynomial.X^2) (1-x))) x := by
  have hg (x : ℝ) : HasDerivAt expNegInvGlue (flatJet (Polynomial.X^2) x) x := by
    have hh := flatJet_hasDerivAt (1:ℚ[X]) x
    have he : flatJet (1:ℚ[X]) = expNegInvGlue := by
      funext y; simp [flatJet]
    rw [he, show flatNext (1:ℚ[X]) = Polynomial.X^2 by simp [flatNext]] at hh
    exact hh
  have hd := (hg x).add ((hg (1-x)).comp x ((hasDerivAt_const x 1).sub (hasDerivAt_id x)))
  convert hd.inv (Real.smoothTransition.pos_denom x).ne' using 1 <;>
    first
    | rfl
    | simp only [transitionReciprocal, zero_sub, mul_neg, mul_one, Pi.add_apply, Function.comp_def]
      field_simp [(Real.smoothTransition.pos_denom x).ne']
      ring

inductive JetExpr where
  | const : ℚ → JetExpr
  | id : JetExpr
  | add : JetExpr → JetExpr → JetExpr
  | mul : JetExpr → JetExpr → JetExpr
  | affine : ℚ → ℚ → JetExpr → JetExpr
  | flat : ℚ[X] → JetExpr
  | reciprocal : JetExpr

namespace JetExpr

def eval : JetExpr → ℝ → ℝ
  | .const q => fun _ => q
  | .id => fun x => x
  | .add f g => fun x => f.eval x + g.eval x
  | .mul f g => fun x => f.eval x * g.eval x
  | .affine a b f => fun x => f.eval ((a:ℝ)*x+b)
  | .flat p => flatJet p
  | .reciprocal => transitionReciprocal

theorem smooth (f : JetExpr) : ContDiff ℝ (⊤ : ℕ∞) f.eval := by
  induction f with
  | const q => exact contDiff_const
  | id => exact contDiff_id
  | add f g hf hg => exact hf.add hg
  | mul f g hf hg => exact hf.mul hg
  | affine a b f hf => exact hf.comp ((contDiff_const.mul contDiff_id).add contDiff_const)
  | flat p => exact flatJet_smooth p
  | reciprocal => exact transitionReciprocal_smooth

def diff : JetExpr → JetExpr
  | .const _ => .const 0
  | .id => .const 1
  | .add f g => .add f.diff g.diff
  | .mul f g => .add (.mul f.diff g) (.mul f g.diff)
  | .affine a b f => .mul (.const a) (.affine a b f.diff)
  | .flat p => .flat (flatNext p)
  | .reciprocal => .mul (.mul (.const (-1)) (.mul .reciprocal .reciprocal))
      (.add (.flat (Polynomial.X^2)) (.mul (.const (-1)) (.affine (-1) 1 (.flat (Polynomial.X^2)))))

theorem diff_correct (f : JetExpr) (x : ℝ) : HasDerivAt f.eval (f.diff.eval x) x := by
  induction f generalizing x with
  | const q => simpa [diff,eval] using hasDerivAt_const x (q:ℝ)
  | id =>
      simp only [diff, eval, Rat.cast_one]
      exact hasDerivAt_id x
  | add f g hf hg => exact (hf x).add (hg x)
  | mul f g hf hg => exact (hf x).mul (hg x)
  | affine a b f hf =>
      convert (hf ((a:ℝ)*x+b)).comp x
        (((hasDerivAt_const x (a:ℝ)).mul (hasDerivAt_id x)).add (hasDerivAt_const x (b:ℝ))) using 1
      all_goals first | rfl | simp [diff,eval,mul_comm]
  | flat p => exact flatJet_hasDerivAt p x
  | reciprocal =>
      simpa [diff, eval, sub_eq_add_neg, add_comm] using transitionReciprocal_hasDerivAt x

def nth (f : JetExpr) : ℕ → JetExpr
  | 0 => f
  | n+1 => (f.nth n).diff

theorem nth_correct (f : JetExpr) (n : ℕ) : (f.nth n).eval = iteratedDeriv n f.eval := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [nth, iteratedDeriv_succ, ← ih]
      exact funext (fun x => ((f.nth n).diff_correct x).deriv.symm)

def bound : JetExpr → ℚ → ℚ
  | .const q, _ => |q|
  | .id, R => |R|
  | .add f g, R => f.bound R + g.bound R
  | .mul f g, R => f.bound R * g.bound R
  | .affine a b f, R => f.bound (|a| * |R| + |b|)
  | .flat p, _ => flatBound p
  | .reciprocal, _ => 16

theorem bound_nonneg (f : JetExpr) (R : ℚ) : 0 ≤ f.bound R := by
  induction f generalizing R with
  | const q => exact abs_nonneg q
  | id => exact abs_nonneg R
  | add f g hf hg => exact add_nonneg (hf _) (hg _)
  | mul f g hf hg => exact mul_nonneg (hf _) (hg _)
  | affine a b f hf => exact hf _
  | flat p => exact flatBound_nonneg p
  | reciprocal => norm_num [bound]

theorem bound_correct (f : JetExpr) (R : ℚ) (x : ℝ) (hx : |x| ≤ |(R:ℝ)|) :
    |f.eval x| ≤ (f.bound R:ℝ) := by
  induction f generalizing R x with
  | const q => simp [eval,bound]
  | id => simpa [eval,bound] using hx
  | add f g hf hg =>
      simpa only [eval,bound,Rat.cast_add] using
        (abs_add_le (f.eval x) (g.eval x)).trans (add_le_add (hf _ _ hx) (hg _ _ hx))
  | mul f g hf hg =>
      simpa only [eval,bound,Rat.cast_mul,abs_mul] using
        mul_le_mul (hf _ _ hx) (hg _ _ hx) (abs_nonneg _) (by exact_mod_cast f.bound_nonneg R)
  | affine a b f hf =>
      apply hf
      simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_abs]
      rw [abs_of_nonneg (by positivity : 0 ≤ |(a:ℝ)| * |(R:ℝ)| + |(b:ℝ)|)]
      exact (abs_add_le _ _).trans (add_le_add
        (by simpa only [abs_mul] using mul_le_mul_of_nonneg_left hx (abs_nonneg (a:ℝ))) le_rfl)
  | flat p => exact flatJet_bound p x
  | reciprocal => exact transitionReciprocal_bound x

theorem nth_bound (f : JetExpr) (n : ℕ) (R : ℚ) (x : ℝ) (hx : |x| ≤ |(R:ℝ)|) :
    |iteratedDeriv n f.eval x| ≤ ((f.nth n).bound R:ℝ) := by
  rw [← nth_correct]
  exact bound_correct _ _ _ hx

end JetExpr

end Solenoidal
end

end OAI
