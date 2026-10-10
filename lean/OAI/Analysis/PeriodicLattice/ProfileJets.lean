import OAI.Analysis.PeriodicLattice.Solenoidal

namespace OAI

/-! Explicit jets and uniform profile derivative estimates. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingProfileJets {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace ProfileJets

open scoped ContDiff
open Polynomial

def rhoTerm (k : ℕ) (x : ℝ) : ℝ := x⁻¹ ^ k * expNegInvGlue x

theorem rhoTerm_contDiff (k : ℕ) : ContDiff ℝ ∞ (rhoTerm k) := by
  change ContDiff ℝ ∞ (fun x : ℝ => x⁻¹ ^ k * expNegInvGlue x)
  simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
    (expNegInvGlue.contDiff_polynomial_eval_inv_mul (n := ⊤) (X ^ k))

theorem rhoTerm_hasDerivAt (k : ℕ) (x : ℝ) :
    HasDerivAt (rhoTerm k) (rhoTerm (k + 2) x - (k : ℝ) * rhoTerm (k + 1) x) x := by
  have hh := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul ((X : ℝ[X]) ^ k) x
  convert hh using 1
  · funext y
    simp only [rhoTerm, Polynomial.eval_pow, Polynomial.eval_X]
  · simp only [rhoTerm, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.derivative_X_pow, Polynomial.eval_C]
    rcases k with _ | k
    · simp
    · simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ]
      ring

theorem rhoTerm_bound (k : ℕ) (x : ℝ) : |rhoTerm k x| ≤ (Nat.factorial k : ℝ) := by
  by_cases hx : x ≤ 0
  · simp only [rhoTerm, expNegInvGlue.zero_of_nonpos hx, mul_zero, abs_zero]
    positivity
  · have hx' : 0 < x := lt_of_not_ge hx
    have h := Real.pow_div_factorial_le_exp (x⁻¹) (inv_nonneg.mpr hx'.le) k
    have hf : (0 : ℝ) < Nat.factorial k := by exact_mod_cast Nat.factorial_pos k
    rw [rhoTerm, expNegInvGlue, ite_eq_right hx, abs_of_nonneg (by positivity), Real.exp_neg]
    rw [← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    exact (div_le_iff₀ hf).mp h |>.trans_eq (mul_comm _ _)

theorem denominator_lower (x : ℝ) :
    (1 : ℝ) / 9 ≤ expNegInvGlue x + expNegInvGlue (1 - x) := by
  have hh : (1 : ℝ) / 9 ≤ expNegInvGlue (1 / 2) := by
    norm_num only [expNegInvGlue, show ¬((1 : ℝ) / 2 ≤ 0) by norm_num, ↓reduceIte, inv_div, inv_one]
    rw [Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (Real.exp_pos _)
    have he := Real.exp_one_lt_three
    have hz := Real.exp_pos 1
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  rcases le_total (1 / 2 : ℝ) x with hx | hx
  · exact hh.trans ((expNegInvGlue.monotone hx).trans (le_add_of_nonneg_right (expNegInvGlue.nonneg _)))
  · exact hh.trans ((expNegInvGlue.monotone (show (1 / 2 : ℝ) ≤ 1 - x by linarith)).trans
      (le_add_of_nonneg_left (expNegInvGlue.nonneg _)))

def denomInv (k : ℕ) (x : ℝ) : ℝ :=
  (expNegInvGlue x + expNegInvGlue (1 - x))⁻¹ ^ k

theorem denomInv_contDiff (k : ℕ) : ContDiff ℝ ∞ (denomInv k) :=
  (expNegInvGlue.contDiff.add (expNegInvGlue.contDiff.comp
    (contDiff_const.sub contDiff_id))).inv (fun x => (Real.smoothTransition.pos_denom x).ne') |>.pow k

theorem denomInv_bound (k : ℕ) (x : ℝ) : |denomInv k x| ≤ (9 : ℝ)^k := by
  have hp := Real.smoothTransition.pos_denom x
  rw [denomInv, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (inv_nonneg.mpr hp.le) ((inv_le_comm₀ hp (by norm_num)).mpr (by simpa using denominator_lower x)) k

theorem denomInv_hasDerivAt (k : ℕ) (x : ℝ) :
    HasDerivAt (denomInv k)
      (-(k : ℝ) * denomInv (k + 1) x * (rhoTerm 2 x - rhoTerm 2 (1-x))) x := by
  have hr (y : ℝ) : HasDerivAt expNegInvGlue (rhoTerm 2 y) y := by
    have he : rhoTerm 0 = expNegInvGlue := by funext z; simp [rhoTerm]
    simpa only [he, Nat.reduceAdd, Nat.cast_zero, zero_mul, sub_zero] using rhoTerm_hasDerivAt 0 y
  have hd := ((hr x).add ((hr (1-x)).comp x ((hasDerivAt_id x).const_sub 1))).inv
    (Real.smoothTransition.pos_denom x).ne'
  have hh := hd.pow k
  change HasDerivAt (denomInv k) _ x at hh
  convert hh using 1
  rcases k with _ | k
  · simp
  · dsimp only [denomInv]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Pi.inv_apply, Pi.add_apply, Function.comp_apply, div_eq_mul_inv]
    rw [← inv_pow]
    simp only [pow_succ]
    ring

abbrev Factor := Bool × ℤ × ℤ × ℕ
abbrev Term := ℤ × List Factor
abbrev Expr := List Term

def evalFactor (f : Factor) (x : ℝ) : ℝ :=
  if f.1 then denomInv f.2.2.2 ((f.2.1 : ℝ) * x + f.2.2.1)
  else rhoTerm f.2.2.2 ((f.2.1 : ℝ) * x + f.2.2.1)

def evalProduct (l : List Factor) (x : ℝ) : ℝ := (l.map (fun f => evalFactor f x)).prod

def evalTerm (t : Term) (x : ℝ) : ℝ := t.1 * evalProduct t.2 x

def eval (e : Expr) (x : ℝ) : ℝ := (e.map (fun t => evalTerm t x)).sum

def factorBound (f : Factor) : ℕ := if f.1 then 9 ^ f.2.2.2 else Nat.factorial f.2.2.2

def productBound (l : List Factor) : ℕ := (l.map factorBound).prod

def termBound (t : Term) : ℕ := t.1.natAbs * productBound t.2

def bound (e : Expr) : ℕ := (e.map termBound).sum

theorem evalFactor_bound (f : Factor) (x : ℝ) : |evalFactor f x| ≤ factorBound f := by
  rcases f with ⟨i, a, c, k⟩
  cases i
  · exact rhoTerm_bound k _
  · simpa [factorBound, evalFactor] using denomInv_bound k ((a : ℝ) * x + c)

theorem evalProduct_bound (l : List Factor) (x : ℝ) : |evalProduct l x| ≤ productBound l := by
  induction l with
  | nil => norm_num [evalProduct, productBound]
  | cons f l ih =>
    simp only [evalProduct, List.map_cons, List.prod_cons, abs_mul, productBound, Nat.cast_mul] at *
    exact mul_le_mul (evalFactor_bound f x) ih (abs_nonneg _) (by positivity)

theorem evalTerm_bound (t : Term) (x : ℝ) : |evalTerm t x| ≤ termBound t := by
  simp only [evalTerm, abs_mul, termBound, Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs]
  exact mul_le_mul_of_nonneg_left (evalProduct_bound t.2 x) (abs_nonneg _)
theorem eval_bound (e : Expr) (x : ℝ) : |eval e x| ≤ bound e := by
  induction e with
  | nil => norm_num [eval, bound]
  | cons t e ih =>
    simp only [eval, List.map_cons, List.sum_cons, bound, Nat.cast_add] at *
    exact (abs_add_le _ _).trans (add_le_add (evalTerm_bound t x) ih)

def multPrefix (c : ℤ) (l : List Factor) (e : Expr) : Expr :=
  e.map (fun t => (c * t.1, l ++ t.2))

def diffFactor (f : Factor) : Expr :=
  if f.1 then
    [(-f.2.1 * f.2.2.2, [(true, f.2.1, f.2.2.1, f.2.2.2 + 1), (false, f.2.1, f.2.2.1, 2)]),
     (f.2.1 * f.2.2.2, [(true, f.2.1, f.2.2.1, f.2.2.2 + 1), (false, -f.2.1, 1-f.2.2.1, 2)])]
  else
    [(f.2.1, [(false, f.2.1, f.2.2.1, f.2.2.2 + 2)]),
     (-f.2.1 * f.2.2.2, [(false, f.2.1, f.2.2.1, f.2.2.2 + 1)])]

def diffProduct : List Factor → Expr
  | [] => []
  | f :: l => multPrefix 1 l (diffFactor f) ++ multPrefix 1 [f] (diffProduct l)

def diffTerm (t : Term) : Expr := multPrefix t.1 [] (diffProduct t.2)

def diff (e : Expr) : Expr := e.flatMap diffTerm

@[simp] theorem eval_nil (x : ℝ) : eval [] x = 0 := rfl

@[simp] theorem eval_cons (t : Term) (e : Expr) (x : ℝ) :
    eval (t :: e) x = evalTerm t x + eval e x := rfl

@[simp] theorem eval_append (e d : Expr) (x : ℝ) : eval (e ++ d) x = eval e x + eval d x := by
  simp [eval]

@[simp] theorem evalProduct_nil (x : ℝ) : evalProduct [] x = 1 := rfl

@[simp] theorem evalProduct_cons (f : Factor) (l : List Factor) (x : ℝ) :
    evalProduct (f :: l) x = evalFactor f x * evalProduct l x := rfl

@[simp] theorem evalProduct_append (l m : List Factor) (x : ℝ) :
    evalProduct (l ++ m) x = evalProduct l x * evalProduct m x := by
  simp [evalProduct]

theorem eval_multPrefix (c : ℤ) (l : List Factor) (e : Expr) (x : ℝ) :
    eval (multPrefix c l e) x = ((c : ℝ) * evalProduct l x) * eval e x := by
  induction e with
  | nil => simp [multPrefix]
  | cons t e ih =>
    simp only [multPrefix, List.map_cons, eval_cons] at *
    rw [ih]
    simp only [evalTerm, evalProduct_append, Int.cast_mul]
    ring

theorem diffFactor_correct (f : Factor) (x : ℝ) :
    HasDerivAt (evalFactor f) (eval (diffFactor f) x) x := by
  rcases f with ⟨i, a, c, k⟩
  have ha : HasDerivAt (fun x : ℝ => (a : ℝ)*x+c) (a : ℝ) x :=
    by
      convert HasDerivAt.add_const (c : ℝ) (HasDerivAt.const_mul (a : ℝ) (hasDerivAt_id x)) using 1 <;> first | rfl | simp
  cases i
  · have hh := (rhoTerm_hasDerivAt k ((a : ℝ)*x+c)).comp x ha
    convert hh using 1 <;> try rfl
    simp only [diffFactor, Bool.false_eq_true, ↓reduceIte, eval_cons, eval_nil, evalTerm,
        evalProduct_cons, evalProduct_nil, evalFactor, Int.cast_neg, Int.cast_mul, Int.cast_natCast]
    ring
  · have hh := (denomInv_hasDerivAt k ((a : ℝ)*x+c)).comp x ha
    convert hh using 1 <;> try rfl
    simp only [diffFactor, ↓reduceIte, eval_cons, eval_nil, evalTerm,
        evalProduct_cons, evalProduct_nil, evalFactor, Bool.false_eq_true,
        Int.cast_neg, Int.cast_mul, Int.cast_natCast, Int.cast_sub, Int.cast_one]
    rw [show -(a : ℝ)*x+(1-c) = 1-((a : ℝ)*x+c) by ring]
    ring

theorem diffProduct_correct (l : List Factor) (x : ℝ) :
    HasDerivAt (evalProduct l) (eval (diffProduct l) x) x := by
  induction l with
  | nil => exact hasDerivAt_const x 1
  | cons f l ih =>
    have hh := (diffFactor_correct f x).mul ih
    convert hh using 1 <;> try rfl
    simp [diffProduct, eval_multPrefix, mul_comm]

theorem diffTerm_correct (t : Term) (x : ℝ) :
    HasDerivAt (evalTerm t) (eval (diffTerm t) x) x := by
  convert (diffProduct_correct t.2 x).const_mul (t.1 : ℝ) using 1 <;> try rfl
  simp [diffTerm, eval_multPrefix]

theorem diff_correct (e : Expr) (x : ℝ) : HasDerivAt (eval e) (eval (diff e) x) x := by
  induction e with
  | nil => exact hasDerivAt_const x 0
  | cons t e ih =>
    convert (diffTerm_correct t x).add ih using 1 <;> try rfl
    simp [diff, List.flatMap_cons]

def jet (e : Expr) (n : ℕ) : Expr := diff^[n] e

theorem jet_correct (e : Expr) (n : ℕ) : eval (jet e n) = iteratedDeriv n (eval e) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [jet, Function.iterate_succ_apply']
    change eval (diff (jet e n)) = _
    rw [iteratedDeriv_succ, ← ih]
    exact funext (fun x => (diff_correct (jet e n) x).deriv.symm)

def clockExpr : Expr := [(1, [(false, 3, -1, 0), (true, 3, -1, 1)])]

def bumpExpr : Expr := [(1, [(false, 8, 3, 0), (true, 8, 3, 1),
  (false, -8, 3, 0), (true, -8, 3, 1)])]

theorem eval_clockExpr : eval clockExpr = Profiles.clock := by
  funext x
  simp [clockExpr, eval, evalTerm, evalProduct, evalFactor, rhoTerm, denomInv,
    Profiles.clock, Real.smoothTransition, div_eq_mul_inv, sub_eq_add_neg]

theorem eval_bumpExpr : eval bumpExpr = Profiles.bump := by
  funext x
  norm_num [bumpExpr, eval, evalTerm, evalProduct, evalFactor, rhoTerm, denomInv,
    Profiles.bump, Real.smoothTransition, div_eq_mul_inv, sub_eq_add_neg]
  ring_nf

def pulseBound (r : ℕ) : ℕ := bound (jet clockExpr (r+1))

def bumpBound (k : ℕ) : ℕ := bound (jet bumpExpr k)

theorem pulseBound_spec (r : ℕ) (t : ℝ) :
    |iteratedDeriv r (deriv Profiles.clock) t| ≤ (pulseBound r : ℝ) := by
  have hc := eval_bound (jet clockExpr (r+1)) t
  rwa [jet_correct, eval_clockExpr, iteratedDeriv_succ'] at hc

theorem bumpBound_spec (k : ℕ) (y : ℝ) :
    |iteratedDeriv k Profiles.bump y| ≤ (bumpBound k : ℝ) := by
  have hc := eval_bound (jet bumpExpr k) y
  rwa [jet_correct, eval_bumpExpr] at hc

end ProfileJets

end
end PeriodicLattice

end OAI
