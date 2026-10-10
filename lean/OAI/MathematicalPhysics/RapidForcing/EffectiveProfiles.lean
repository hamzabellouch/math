import OAI.MathematicalPhysics.RapidForcing.SchwartzRestriction

namespace OAI

section

open scoped BigOperators Polynomial Topology
open Set Filter

namespace RapidForcing
namespace EffectiveProfile

abbrev GluePoly := List (ℚ × ℕ)

def glueDiff : GluePoly → GluePoly
  | [] => []
  | (a, n) :: p => (a, n + 2) :: (-(n : ℚ) * a, n + 1) :: glueDiff p

def glueBound : GluePoly → ℚ
  | [] => 0
  | (a, n) :: p => |a| * (n.factorial : ℚ) + glueBound p

noncomputable def monoGlue (n : ℕ) (x : ℝ) : ℝ := x⁻¹ ^ n * expNegInvGlue x

noncomputable def glue : GluePoly → ℝ → ℝ
  | [], _ => 0
  | (a, n) :: p, x => (a : ℝ) * monoGlue n x + glue p x

lemma glueBound_nonneg (p : GluePoly) : 0 ≤ glueBound p := by
  induction p with
  | nil => rfl
  | cons a p ih => rcases a with ⟨a, n⟩; dsimp [glueBound]; positivity

lemma hasDerivAt_monoGlue (n : ℕ) (x : ℝ) :
    HasDerivAt (monoGlue n) (monoGlue (n + 2) x - n * monoGlue (n + 1) x) x := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul ((Polynomial.X : ℝ[X]) ^ n) x
  simp only [Polynomial.derivative_X_pow, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at h
  convert! h using 1
  · cases n with
    | zero => simp [monoGlue]
    | succ n => simp [monoGlue, pow_add]; ring

lemma hasDerivAt_glue (p : GluePoly) (x : ℝ) :
    HasDerivAt (glue p) (glue (glueDiff p) x) x := by
  induction p with
  | nil => exact hasDerivAt_const _ _
  | cons a p ih =>
    rcases a with ⟨a, n⟩
    change HasDerivAt (fun y => (a : ℝ) * monoGlue n y + glue p y) _ x
    convert! ((hasDerivAt_monoGlue n x).const_mul (a : ℝ)).add ih using 1
    simp [glueDiff, glue]; ring

lemma contDiff_glue (p : GluePoly) : ContDiff ℝ (⊤ : ℕ∞) (glue p) := by
  induction p with
  | nil => exact contDiff_const
  | cons a p ih =>
    rcases a with ⟨a, n⟩
    have hm : ContDiff ℝ (⊤ : ℕ∞) (monoGlue n) := by
      change ContDiff ℝ (⊤ : ℕ∞) (fun x => x⁻¹ ^ n * expNegInvGlue x)
      simpa using
        expNegInvGlue.contDiff_polynomial_eval_inv_mul ((Polynomial.X : ℝ[X]) ^ n)
    exact (contDiff_const.mul hm).add ih

lemma pow_mul_exp_neg_le (y : ℝ) (hy : 0 ≤ y) (n : ℕ) :
    y ^ n * Real.exp (-y) ≤ n.factorial := by
  have h := mul_le_mul_of_nonneg_right (Real.pow_div_factorial_le_exp y hy n)
    (Real.exp_pos (-y)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
  have hn : (0 : ℝ) < n.factorial := by positivity
  have h' : (y ^ n * Real.exp (-y)) / n.factorial ≤ 1 := by
    simpa only [mul_div_right_comm] using h
  simpa only [one_mul] using (div_le_iff₀ hn).mp h'

lemma abs_monoGlue_le (n : ℕ) (x : ℝ) : |monoGlue n x| ≤ (n.factorial : ℝ) := by
  by_cases hx : x ≤ 0
  · simp only [monoGlue, expNegInvGlue.zero_of_nonpos hx, mul_zero, abs_zero]
    positivity
  have hi : 0 ≤ x⁻¹ := (inv_pos.mpr (lt_of_not_ge hx)).le
  simpa only [monoGlue, expNegInvGlue, ite_eq_right hx,
    abs_of_nonneg (mul_nonneg (pow_nonneg hi n) (Real.exp_pos _).le)] using
    pow_mul_exp_neg_le x⁻¹ hi n

lemma abs_glue_le (p : GluePoly) (x : ℝ) : |glue p x| ≤ (glueBound p : ℝ) := by
  induction p with
  | nil => simp [glue, glueBound]
  | cons a p ih =>
    rcases a with ⟨a, n⟩
    rw [glue]
    refine (abs_add_le _ _).trans ?_
    simpa only [glueBound, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_abs, abs_mul] using
      add_le_add (mul_le_mul_of_nonneg_left (abs_monoGlue_le n x) (abs_nonneg (a : ℝ))) ih

lemma glue_one : glue [(1, 0)] = expNegInvGlue := by
  ext x
  simp [glue, monoGlue]

lemma denominator_lower (x : ℝ) :
    (1 / 16 : ℝ) ≤ expNegInvGlue x + expNegInvGlue (1 - x) := by
  have he : Real.exp 2 < 16 := by
    calc
      Real.exp 2 = Real.exp 1 ^ 2 := by simp [← Real.exp_nat_mul]
      _ < 3 ^ 2 := pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le (by decide)
      _ < 16 := by norm_num
  have hb : (1 / 16 : ℝ) ≤ expNegInvGlue (1 / 2) := by
    norm_num [expNegInvGlue, Real.exp_neg] at ⊢
    simpa only [one_div] using (inv_le_inv₀ (by norm_num : (0 : ℝ) < 16) (Real.exp_pos 2)).mpr he.le
  have hmono := expNegInvGlue.monotone
  rcases le_total (1 / 2 : ℝ) x with hx | hx
  · exact hb.trans ((hmono hx).trans (le_add_of_nonneg_right (expNegInvGlue.nonneg _)))
  · exact hb.trans ((hmono (show (1 / 2 : ℝ) ≤ 1 - x by linarith)).trans
      (le_add_of_nonneg_left (expNegInvGlue.nonneg _)))

inductive Expr where
  | const : ℚ → Expr
  | left : GluePoly → Expr
  | right : GluePoly → Expr
  | invDen : ℕ → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr

noncomputable def Expr.value : Expr → ℝ → ℝ
  | .const q, _ => q
  | .left p, x => glue p x
  | .right p, x => glue p (1 - x)
  | .invDen n, x => (expNegInvGlue x + expNegInvGlue (1 - x))⁻¹ ^ n
  | .add a b, x => a.value x + b.value x
  | .mul a b, x => a.value x * b.value x

def Expr.bound : Expr → ℚ
  | .const q => |q|
  | .left p => glueBound p
  | .right p => glueBound p
  | .invDen n => 16 ^ n
  | .add a b => a.bound + b.bound
  | .mul a b => a.bound * b.bound

def Expr.diff : Expr → Expr
  | .const _ => .const 0
  | .left p => .left (glueDiff p)
  | .right p => .mul (.const (-1)) (.right (glueDiff p))
  | .invDen n => .mul (.mul (.const (-(n : ℚ)))
      (.add (.left (glueDiff [(1, 0)])) (.mul (.const (-1)) (.right (glueDiff [(1, 0)])))))
      (.invDen (n + 1))
  | .add a b => .add a.diff b.diff
  | .mul a b => .add (.mul a.diff b) (.mul a b.diff)

lemma Expr.bound_nonneg (e : Expr) : 0 ≤ e.bound := by
  induction e with
  | const q => exact abs_nonneg q
  | left p => exact glueBound_nonneg p
  | right p => exact glueBound_nonneg p
  | invDen n => change 0 ≤ (16 : ℚ) ^ n; positivity
  | add a b ha hb => exact add_nonneg ha hb
  | mul a b ha hb => exact mul_nonneg ha hb

lemma Expr.abs_value_le (e : Expr) (x : ℝ) : |e.value x| ≤ (e.bound : ℝ) := by
  induction e with
  | const q => simp [value, bound]
  | left p => exact abs_glue_le p x
  | right p => exact abs_glue_le p (1 - x)
  | invDen n =>
    have hd := denominator_lower x
    have hp := Real.smoothTransition.pos_denom x
    have hi : (expNegInvGlue x + expNegInvGlue (1 - x))⁻¹ ≤ 16 := by
      simpa using (inv_le_inv₀ hp (by norm_num : (0 : ℝ) < 1 / 16)).2 hd
    simpa only [value, bound, Rat.cast_pow, Rat.cast_ofNat,
      abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hp.le) n)] using
        pow_le_pow_left₀ (inv_nonneg.mpr hp.le) hi n
  | add a b ha hb =>
    exact (abs_add_le _ _).trans (by simpa [bound] using add_le_add ha hb)
  | mul a b ha hb =>
    simpa [value, bound, abs_mul] using
      mul_le_mul ha hb (abs_nonneg _) (by exact_mod_cast a.bound_nonneg)

lemma Expr.hasDerivAt (e : Expr) (x : ℝ) : HasDerivAt e.value (e.diff.value x) x := by
  induction e with
  | const q => simpa [diff, value] using hasDerivAt_const x (q : ℝ)
  | left p => exact hasDerivAt_glue p x
  | right p =>
    convert! (hasDerivAt_glue p (1 - x)).comp x ((hasDerivAt_id x).const_sub 1) using 1
    simp [diff, value, mul_comm]
  | invDen n =>
    have hl : HasDerivAt expNegInvGlue (glue (glueDiff [(1, 0)]) x) x := by
      simpa [glue_one, Function.comp_def] using hasDerivAt_glue [(1, 0)] x
    have hr : HasDerivAt (fun y => expNegInvGlue (1 - y))
        (-(glue (glueDiff [(1, 0)]) (1 - x))) x := by
      simpa [glue_one, Function.comp_def] using (hasDerivAt_glue [(1, 0)] (1 - x)).comp x
        ((hasDerivAt_id x).const_sub 1)
    let d : ℝ → ℝ := fun y => expNegInvGlue y + expNegInvGlue (1 - y)
    let a : ℝ := glue (glueDiff [(1, 0)]) x - glue (glueDiff [(1, 0)]) (1 - x)
    have hd : HasDerivAt d a x := by
      convert! hl.add hr using 1
    have hp : d x ≠ 0 := (Real.smoothTransition.pos_denom x).ne'
    have hinv : HasDerivAt (fun y => (d y)⁻¹) (-a * (d x)⁻¹ ^ 2) x := by
      convert! hd.inv hp using 1
      simp [div_eq_mul_inv, inv_pow]
    have hpow (k : ℕ) : HasDerivAt (fun y => (d y)⁻¹ ^ k)
        (-(k : ℝ) * a * (d x)⁻¹ ^ (k + 1)) x := by
      induction k with
      | zero => simpa using hasDerivAt_const x (1 : ℝ)
      | succ k ih =>
        convert! ih.mul hinv using 1
        simp only [Nat.cast_add, Nat.cast_one, pow_succ]; ring
    simpa only [diff, value, Rat.cast_neg, Rat.cast_natCast, Rat.cast_one,
      neg_mul, one_mul, mul_neg, sub_eq_add_neg, d, a] using hpow n
  | add a b ha hb => exact ha.add hb
  | mul a b ha hb => exact ha.mul hb

lemma Expr.contDiff (e : Expr) : ContDiff ℝ (⊤ : ℕ∞) e.value := by
  induction e with
  | const q => exact contDiff_const
  | left p => exact contDiff_glue p
  | right p => exact (contDiff_glue p).comp (contDiff_const.sub contDiff_id)
  | invDen n =>
    exact ((@expNegInvGlue.contDiff ⊤).add
      (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))).inv
        (fun x => (Real.smoothTransition.pos_denom x).ne') |>.pow n
  | add a b ha hb => exact ha.add hb
  | mul a b ha hb => exact ha.mul hb

lemma Expr.lipschitz (e : Expr) :
    LipschitzWith ⟨(e.diff.bound : ℝ), by exact_mod_cast e.diff.bound_nonneg⟩ e.value := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (e.hasDerivAt x).differentiableAt)
  intro x
  change ‖deriv e.value x‖ ≤ (e.diff.bound : ℝ)
  rw [(e.hasDerivAt x).deriv, Real.norm_eq_abs]
  exact e.diff.abs_value_le x

def switchExpr (n : ℕ) : Expr :=
  Expr.diff^[n] (.mul (.left [(1, 0)]) (.invDen 1))

lemma switchExpr_value (n : ℕ) :
    (switchExpr n).value = iteratedDeriv n Real.smoothTransition := by
  induction n with
  | zero =>
    ext x
    simp [switchExpr, Expr.value, glue_one, Real.smoothTransition, div_eq_mul_inv]
  | succ n ih =>
    rw [iteratedDeriv_succ, ← ih]
    ext x
    simp only [switchExpr, Function.iterate_succ_apply']
    exact ((switchExpr n).hasDerivAt x).deriv.symm

end EffectiveProfile
end RapidForcing

end

end OAI
