import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Expanding
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.CenterPaths
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailDifferentiability

namespace OAI

noncomputable section
namespace VelocityDetection.Effective
open Polynomial Set Function Filter
open scoped BigOperators Topology ContDiff

abbrev Poly := List (ℕ × ℚ)

noncomputable def poly : Poly → Polynomial ℝ
  | [] => 0
  | (k,q)::ps => Polynomial.C (q:ℝ)*Polynomial.X^k + poly ps

def nextPoly : Poly → Poly
  | [] => []
  | (k,q)::ps => (k+2,q)::(k+1,-q*k)::nextPoly ps

noncomputable def flat (p : Poly) (x : ℝ) : ℝ :=
  (poly p).eval x⁻¹ * expNegInvGlue x

theorem poly_next (p : Poly) : poly (nextPoly p) = X^2*(poly p-(poly p).derivative) := by
  induction p with
  | nil => simp [poly,nextPoly]
  | cons kq ps ih =>
    rcases kq with ⟨k,q⟩
    simp only [poly,nextPoly,ih,Polynomial.derivative_add,Polynomial.derivative_C_mul,
      Polynomial.derivative_X_pow,Rat.cast_mul,Rat.cast_neg,Rat.cast_natCast]
    cases k with
    | zero => simp; ring
    | succ k => simp only [Nat.succ_sub_one,Nat.cast_add,Nat.cast_one,pow_succ,map_mul,map_add,map_neg,map_one]; ring

theorem hasDerivAt_flat (p : Poly) (x : ℝ) :
    HasDerivAt (flat p) (flat (nextPoly p) x) x := by
  change HasDerivAt (fun y => (poly p).eval y⁻¹ * expNegInvGlue y)
    ((poly (nextPoly p)).eval x⁻¹ * expNegInvGlue x) x
  rw [poly_next]
  exact expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (poly p) x

@[fun_prop] theorem contDiff_flat (p : Poly) : ContDiff ℝ ∞ (flat p) :=
  expNegInvGlue.contDiff_polynomial_eval_inv_mul _

def polyBound : Poly → ℚ
  | [] => 0
  | (k,q)::ps => |q| *k.factorial + polyBound ps

theorem polyBound_nonneg (p : Poly) : 0 ≤ polyBound p := by
  induction p with
  | nil => rfl
  | cons kq ps ih =>
    rcases kq with ⟨k,q⟩
    exact add_nonneg (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) ih

theorem monomial_exp_bound (y : ℝ) (hy : 0 ≤ y) (k : ℕ) :
    y^k * Real.exp (-y) ≤ k.factorial := by
  have h := Real.pow_div_factorial_le_exp y hy k
  have hf : (0:ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have he : 0 < Real.exp y := Real.exp_pos _
  rw [div_le_iff₀ hf] at h
  rw [Real.exp_neg,← div_eq_mul_inv,div_le_iff₀ he]
  nlinarith

theorem flat_bound (p : Poly) (x : ℝ) : |flat p x| ≤ (polyBound p:ℝ) := by
  by_cases hx : x ≤ 0
  · simp only [flat,expNegInvGlue.zero_of_nonpos hx,mul_zero,abs_zero]
    exact_mod_cast polyBound_nonneg p
  have hx' : 0 < x := lt_of_not_ge hx
  induction p with
  | nil => simp [flat,poly,polyBound]
  | cons kq ps ih =>
    rcases kq with ⟨k,q⟩
    have he : flat ((k,q)::ps) x = (q:ℝ)*x⁻¹^k*Real.exp (-x⁻¹)+flat ps x := by
      simp [flat,poly,expNegInvGlue,ite_eq_right hx,add_mul]
    rw [he]
    calc
      |(q:ℝ)*x⁻¹^k*Real.exp (-x⁻¹)+flat ps x| ≤
          |(q:ℝ)*x⁻¹^k*Real.exp (-x⁻¹)|+|flat ps x| := abs_add_le _ _
      _ ≤ |(q:ℝ)| *(k.factorial:ℝ)+(polyBound ps:ℝ) := by
        apply add_le_add _ ih
        rw [abs_mul,abs_mul,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hx'.le) _),
          abs_of_pos (Real.exp_pos _),mul_assoc]
        exact mul_le_mul_of_nonneg_left (monomial_exp_bound x⁻¹ (inv_nonneg.mpr hx'.le) k)
          (abs_nonneg (q:ℝ))
      _ = (polyBound ((k,q)::ps):ℝ) := by simp [polyBound]

theorem flat_lipschitz (p : Poly) (x y : ℝ) :
    |flat p x-flat p y| ≤ (polyBound (nextPoly p):ℝ)*|x-y| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := flat p) (f' := flat (nextPoly p)) (s := (Set.univ : Set ℝ))
    (fun z _ => (hasDerivAt_flat p z).hasDerivWithinAt)
    (fun z _ => by simpa only [Real.norm_eq_abs] using flat_bound (nextPoly p) z)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using h

@[simp] theorem flat_zero (p : Poly) : flat p 0 = 0 := by simp [flat]

inductive Expr (n : ℕ) where
  | rat : ℚ → Expr n
  | var : Fin n → Expr n
  | add : Expr n → Expr n → Expr n
  | neg : Expr n → Expr n
  | mul : Expr n → Expr n → Expr n
  | inv : Expr n → Expr n
  | flat : Poly → Expr n → Expr n
  deriving Inhabited

end VelocityDetection.Effective
end

noncomputable section
namespace VelocityDetection.Effective.Expr
open Polynomial Set Function Filter
open scoped BigOperators Topology ContDiff
variable {n : ℕ}

noncomputable def eval (x : Fin n → ℝ) : Expr n → ℝ
  | .rat q => q
  | .var i => x i
  | .add a b => a.eval x + b.eval x
  | .neg a => -a.eval x
  | .mul a b => a.eval x * b.eval x
  | .inv a => (a.eval x)⁻¹
  | .flat p a => Effective.flat p (a.eval x)

def Valid (x : Fin n → ℝ) : Expr n → Prop
  | .rat _ => True
  | .var _ => True
  | .add a b => a.Valid x ∧ b.Valid x
  | .neg a => a.Valid x
  | .mul a b => a.Valid x ∧ b.Valid x
  | .inv a => a.Valid x ∧ a.eval x ≠ 0
  | .flat _ a => a.Valid x

def diff (i : Fin n) : Expr n → Expr n
  | .rat _ => .rat 0
  | .var j => .rat (if i=j then 1 else 0)
  | .add a b => .add (a.diff i) (b.diff i)
  | .neg a => .neg (a.diff i)
  | .mul a b => .add (.mul (a.diff i) b) (.mul a (b.diff i))
  | .inv a => .neg (.mul (a.diff i) (.mul (.inv a) (.inv a)))
  | .flat p a => .mul (.flat (nextPoly p) a) (a.diff i)

theorem valid_diff {x : Fin n → ℝ} (e : Expr n) (h : e.Valid x) (i : Fin n) :
    (e.diff i).Valid x := by
  induction e with
  | rat | var => trivial
  | add a b ha hb => exact ⟨ha h.1,hb h.2⟩
  | neg a ha => exact ha h
  | mul a b ha hb => exact ⟨⟨ha h.1,h.2⟩,⟨h.1,hb h.2⟩⟩
  | inv a ha => exact ⟨ha h.1,⟨h,h⟩⟩
  | flat p a ha => exact ⟨h,ha h⟩

theorem continuousAt_eval {x : Fin n → ℝ} (e : Expr n) (h : e.Valid x) :
    ContinuousAt (fun y => e.eval y) x := by
  induction e with
  | rat => exact continuousAt_const
  | var i => exact (continuous_apply i).continuousAt
  | add a b ha hb => exact (ha h.1).add (hb h.2)
  | neg a ha => exact (ha h).neg
  | mul a b ha hb => exact (ha h.1).mul (hb h.2)
  | inv a ha => exact (ha h.1).inv₀ h.2
  | flat p a ha => exact (contDiff_flat p).continuous.continuousAt.comp (ha h)

theorem valid_eventually {x : Fin n → ℝ} (e : Expr n) (h : e.Valid x) :
    ∀ᶠ y in 𝓝 x, e.Valid y := by
  induction e with
  | rat | var => exact Filter.Eventually.of_forall (fun _ => trivial)
  | add a b ha hb | mul a b ha hb => exact (ha h.1).and (hb h.2)
  | neg a ha | flat _ a ha => exact ha h
  | inv a ha => exact (ha h.1).and ((a.continuousAt_eval h.1).eventually_ne h.2)

theorem hasDerivAt_eval {x : Fin n → ℝ} (e : Expr n) (h : e.Valid x) (i : Fin n) :
    HasDerivAt (fun s => e.eval (Function.update x i s)) ((e.diff i).eval x) (x i) := by
  induction e with
  | rat q => simpa only [diff,eval,Rat.cast_zero] using hasDerivAt_const (x i) (q:ℝ)
  | var j =>
    by_cases hij : i=j
    · subst j
      convert! hasDerivAt_id (x i) using 1 <;> simp [eval,diff]
      rfl
    · simpa [eval,diff,hij,Ne.symm hij] using hasDerivAt_const (x i) (x j)
  | add a b ha hb => exact (ha h.1).add (hb h.2)
  | neg a ha => exact (ha h).neg
  | mul a b ha hb =>
    convert! (ha h.1).mul (hb h.2) using 1
    first | rfl | simp only [Function.update_eq_self,diff,eval]
  | inv a ha =>
    convert! (ha h.1).inv (by simpa only [Function.update_eq_self] using h.2) using 1
    try rfl
    simp only [diff,eval,Function.update_eq_self]
    ring
  | flat p a ha =>
    have hh := ha h
    have he : Function.update x i (x i) = x := Function.update_eq_self _ _
    have hf := hasDerivAt_flat p (a.eval (Function.update x i (x i)))
    convert! hf.comp (x i) hh using 1
    first | rfl | simp only [he,diff,eval]

def jet : List (Fin n) → Expr n → Expr n
  | [], e => e
  | i::is, e => jet is (e.diff i)

theorem valid_jet {x : Fin n → ℝ} (e : Expr n) (h : e.Valid x) (is : List (Fin n)) :
    (e.jet is).Valid x := by
  induction is generalizing e with
  | nil => exact h
  | cons i is ih => exact ih _ (e.valid_diff h i)

end VelocityDetection.Effective.Expr
end

noncomputable section
namespace VelocityDetection.Effective
open Set Filter Function
open scoped BigOperators Topology

structure Ball where
  center : ℚ
  radius : ℚ
  deriving Inhabited

def Ball.Certifies (b : Ball) (x : ℝ) : Prop :=
  0 ≤ b.radius ∧ |x-(b.center:ℝ)| ≤ (b.radius:ℝ)

def polyEval : Poly → ℚ → ℚ
  | [], _ => 0
  | (k,q)::ps, x => q*x^k+polyEval ps x

theorem cast_polyEval (p : Poly) (q : ℚ) :
    (polyEval p q:ℝ) = (poly p).eval (q:ℝ) := by
  induction p with
  | nil => simp [polyEval,poly]
  | cons kq ps ih =>
    rcases kq with ⟨k,c⟩
    simp [polyEval,poly,ih]

def expSum (q : ℚ) (n : ℕ) : ℚ := ∑ k ∈ Finset.range n, q^k / k.factorial

def expError (q : ℚ) (n : ℕ) : ℚ := |q|^n / n.factorial * 2

theorem expError_nonneg (q : ℚ) (n : ℕ) : 0 ≤ expError q n := by unfold expError; positivity

theorem exp_error {q : ℚ} {n : ℕ} (h : |q|/(n+1) ≤ (1/2:ℚ)) :
    |Real.exp (q:ℝ)-(expSum q n:ℝ)| ≤ (expError q n:ℝ) := by
  have hh : ‖(q:ℂ)‖/(n+1:ℝ) ≤ 1/2 := by
    rw [← Complex.ofReal_ratCast,Complex.norm_real,Real.norm_eq_abs]
    have hh : ((|q|/(n+1):ℚ):ℝ) ≤ ((1/2:ℚ):ℝ) := Rat.cast_le.mpr h
    simpa only [Rat.cast_div,Rat.cast_abs,Rat.cast_add,Rat.cast_natCast,Rat.cast_one,
      Rat.cast_ofNat] using hh
  have hc := Complex.exp_bound' (x := (q:ℂ)) (n := n) (by simpa using hh)
  have he : Complex.exp (q:ℂ)-(∑ k ∈ Finset.range n, (q:ℂ)^k/k.factorial) =
      Complex.ofReal (Real.exp (q:ℝ)-(expSum q n:ℝ)) := by
    simp [expSum,Complex.ofReal_sub,Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_pow,
      Complex.ofReal_exp]
  rw [he,Complex.norm_real,Real.norm_eq_abs,← Complex.ofReal_ratCast,Complex.norm_real,
    Real.norm_eq_abs] at hc
  simpa only [expError,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_abs,Rat.cast_natCast,
    Rat.cast_ofNat] using hc

def flatRound (p : Poly) (q : ℚ) (n : ℕ) : Ball :=
  if q ≤ 0 then ⟨0,0⟩ else
  if |q⁻¹|/(n+1) ≤ (1/2:ℚ) ∧
      |polyEval p q⁻¹| *expError (-q⁻¹) n ≤ polyBound (nextPoly p)*|q| then
    ⟨polyEval p q⁻¹*expSum (-q⁻¹) n,|polyEval p q⁻¹| *expError (-q⁻¹) n⟩
  else ⟨0,polyBound (nextPoly p)*|q|⟩

theorem flatRound_certifies (p : Poly) (q : ℚ) (n : ℕ) :
    (flatRound p q n).Certifies (flat p (q:ℝ)) := by
  unfold flatRound
  split_ifs with hq he
  · refine ⟨le_rfl,?_⟩
    have hh : (q:ℝ) ≤ 0 := by exact_mod_cast hq
    simp [flat,expNegInvGlue.zero_of_nonpos hh]
  · refine ⟨mul_nonneg (abs_nonneg _) (expError_nonneg _ _),?_⟩
    have hp : (0:ℝ) < q := by exact_mod_cast lt_of_not_ge hq
    have hh := exp_error (q := -q⁻¹) (n := n) (by simpa only [abs_neg] using he.1)
    simp only [flat,expNegInvGlue,ite_eq_right (not_le_of_gt hp),
      Rat.cast_mul,cast_polyEval,Rat.cast_inv]
    rw [← mul_sub,abs_mul]
    convert mul_le_mul_of_nonneg_left hh (abs_nonneg ((poly p).eval (q:ℝ)⁻¹)) using 1 <;>
      first | rfl | simp only [Rat.cast_neg,Rat.cast_inv,Rat.cast_abs,cast_polyEval]
  · refine ⟨mul_nonneg (polyBound_nonneg _) (abs_nonneg _),?_⟩
    simpa only [Ball.center,Ball.radius,Rat.cast_zero,sub_zero,flat_zero,Rat.cast_mul,Rat.cast_abs]
      using flat_lipschitz p (q:ℝ) 0

theorem flatRound_radius_nonneg (p : Poly) (q : ℚ) (n : ℕ) :
    0 ≤ (flatRound p q n).radius := (flatRound_certifies p q n).1

theorem flatRound_small_bound (p : Poly) (q : ℚ) (n : ℕ) :
    (flatRound p q n).radius ≤ polyBound (nextPoly p)*|q| := by
  unfold flatRound
  split_ifs with hq he
  · exact mul_nonneg (polyBound_nonneg _) (abs_nonneg _)
  · exact he.2
  · exact le_rfl

theorem flatRound_exp_bound (p : Poly) {q : ℚ} (hq : 0 < q) (n : ℕ)
    (he : |q⁻¹|/(n+1) ≤ (1/2:ℚ)) :
    (flatRound p q n).radius ≤ |polyEval p q⁻¹| *expError (-q⁻¹) n := by
  unfold flatRound
  rw [ite_eq_right (not_le_of_gt hq)]
  split_ifs with h
  · exact le_rfl
  · exact le_of_lt (lt_of_not_ge (fun hh => h ⟨he,hh⟩))

theorem flatRound_nonpos (p : Poly) {q : ℚ} (hq : q ≤ 0) (n : ℕ) :
    flatRound p q n = ⟨0,0⟩ := by simp only [flatRound,ite_eq_left hq]

theorem flatRound_radius_tendsto (p : Poly) {q : ℕ → ℚ} {x : ℝ}
    (hq : Tendsto (fun n => (q n:ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n => ((flatRound p (q n) n).radius:ℝ)) atTop (𝓝 0) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have he := hq.eventually_lt_const hx
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    rw [flatRound_nonpos p (by exact_mod_cast hn.le)]
    norm_num
  · apply squeeze_zero (fun n => by exact_mod_cast flatRound_radius_nonneg p (q n) n)
      (g := fun n => (polyBound (nextPoly p):ℝ)*|(q n:ℝ)|)
      (fun n => by exact_mod_cast flatRound_small_bound p (q n) n)
    simpa using hq.abs.const_mul (polyBound (nextPoly p):ℝ)
  · have hi := hq.inv₀ (ne_of_gt hx)
    have hi_abs : Tendsto (fun n => |((q n)⁻¹:ℚ)|.cast) atTop (𝓝 |x⁻¹|) := by
      simpa only [Rat.cast_inv,Rat.cast_abs] using hi.abs
    have hb := hi_abs.eventually_lt_const (show |x⁻¹| < |x⁻¹|+1 by linarith)
    have hp := hq.eventually_const_lt hx
    let C : ℝ := |x⁻¹|+1
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hf : Tendsto (fun n : ℕ => C^n/(n.factorial:ℝ)) atTop (𝓝 0) :=
      FloorSemiring.tendsto_pow_div_factorial_atTop C
    have he : Tendsto (fun n => (expError (-(q n)⁻¹) n:ℝ)) atTop (𝓝 0) := by
      apply squeeze_zero' (g := fun n : ℕ => C^n/(n.factorial:ℝ)*2)
        (Filter.Eventually.of_forall (fun n => by exact_mod_cast expError_nonneg (-(q n)⁻¹) n))
        (by
          filter_upwards [hb] with n hn
          simp only [expError,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_abs,
            Rat.cast_inv,Rat.cast_natCast,Rat.cast_ofNat,abs_neg]
          gcongr
          simpa only [Rat.cast_abs,Rat.cast_inv] using hn.le)
        (by simpa using hf.mul_const 2)
    have hv : Tendsto (fun n => (polyEval p (q n)⁻¹:ℝ)) atTop (𝓝 ((poly p).eval x⁻¹)) := by
      simpa only [cast_polyEval,Rat.cast_inv,Function.comp_def] using ((poly p).continuous.tendsto x⁻¹).comp hi
    have he' : Tendsto (fun n => (|polyEval p (q n)⁻¹| *expError (-(q n)⁻¹) n:ℝ)) atTop (𝓝 0) := by
      simpa only [Rat.cast_mul,Rat.cast_abs,mul_zero] using hv.abs.mul he
    have hden : Tendsto (fun n : ℕ => (n+1:ℝ)) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have hr : Tendsto (fun n : ℕ => C/(n+1:ℝ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
        (tendsto_inv_atTop_zero.comp hden).const_mul C
    have hs := hr.eventually_lt_const (show (0:ℝ)<1/2 by norm_num)
    apply squeeze_zero' (g := fun n => (|polyEval p (q n)⁻¹| *expError (-(q n)⁻¹) n:ℝ))
      (Filter.Eventually.of_forall (fun n => by exact_mod_cast flatRound_radius_nonneg p (q n) n))
      (by
        filter_upwards [hp,hb,hs] with n hpn hbn hsn
        have hrn : |(q n)⁻¹|/(n+1) ≤ (1/2:ℚ) := by
          have hd : (0:ℝ) < (n:ℝ)+1 := by positivity
          have hh : ((|(q n)⁻¹|/(n+1):ℚ):ℝ) < ((1/2:ℚ):ℝ) := by
            simpa only [Rat.cast_div,Rat.cast_add,Rat.cast_natCast,Rat.cast_one,Rat.cast_ofNat]
              using (div_le_div_of_nonneg_right hbn.le hd.le).trans_lt hsn
          exact Rat.cast_le.mp hh.le
        exact_mod_cast flatRound_exp_bound p (by exact_mod_cast hpn) n hrn)
      he'

end VelocityDetection.Effective
end

noncomputable section
namespace VelocityDetection.Effective.Ball
open Set Filter Function
open scoped Topology

def atom (q : ℚ) : Ball := ⟨q,0⟩

def add (a b : Ball) : Ball := ⟨a.center+b.center,a.radius+b.radius⟩

def neg (a : Ball) : Ball := ⟨-a.center,a.radius⟩

def mul (a b : Ball) : Ball :=
  ⟨a.center*b.center,|a.center| *b.radius+|b.center| *a.radius+a.radius*b.radius⟩

def inv (a : Ball) : Ball :=
  ⟨a.center⁻¹,a.radius/(|a.center| *(|a.center|-a.radius))⟩

def invSafe (a : Ball) : Bool := decide (a.radius < |a.center|)

def flat (p : Poly) (a : Ball) (k : ℕ) : Ball :=
  let b := flatRound p a.center k
  ⟨b.center,b.radius+polyBound (nextPoly p)*a.radius⟩

theorem certifies_atom (q : ℚ) : (atom q).Certifies (q:ℝ) := by
  simp [atom,Certifies]

theorem certifies_add {a b : Ball} {x y : ℝ} (ha : a.Certifies x) (hb : b.Certifies y) :
    (a.add b).Certifies (x+y) := by
  refine ⟨add_nonneg ha.1 hb.1,?_⟩
  change |x+y-((a.center+b.center:ℚ):ℝ)| ≤ ((a.radius+b.radius:ℚ):ℝ)
  rw [Rat.cast_add,Rat.cast_add,show x+y-((a.center:ℝ)+(b.center:ℝ)) =
    (x-(a.center:ℝ))+(y-(b.center:ℝ)) by ring]
  exact (abs_add_le _ _).trans (add_le_add ha.2 hb.2)

theorem certifies_neg {a : Ball} {x : ℝ} (ha : a.Certifies x) :
    a.neg.Certifies (-x) := by
  refine ⟨ha.1,?_⟩
  simpa only [neg,Rat.cast_neg,neg_sub_neg,abs_sub_comm] using ha.2

theorem certifies_mul {a b : Ball} {x y : ℝ} (ha : a.Certifies x) (hb : b.Certifies y) :
    (a.mul b).Certifies (x*y) := by
  refine ⟨add_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) hb.1)
    (mul_nonneg (abs_nonneg _) ha.1)) (mul_nonneg ha.1 hb.1),?_⟩
  simp only [mul,Rat.cast_mul,Rat.cast_add,Rat.cast_abs]
  have he : x*y-(a.center:ℝ)*(b.center:ℝ) =
      (a.center:ℝ)*(y-(b.center:ℝ))+(b.center:ℝ)*(x-(a.center:ℝ))+
        (x-(a.center:ℝ))*(y-(b.center:ℝ)) := by ring
  rw [he]
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) ?_)
  · simp only [abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hb.2 (abs_nonneg _))
      (mul_le_mul_of_nonneg_left ha.2 (abs_nonneg _))
  · rw [abs_mul]
    exact mul_le_mul ha.2 hb.2 (abs_nonneg _) (by exact_mod_cast ha.1)

theorem certifies_inv {a : Ball} {x : ℝ} (ha : a.Certifies x) (hs : a.invSafe = true) :
    a.inv.Certifies x⁻¹ := by
  have hs' : a.radius < |a.center| := of_decide_eq_true hs
  have hc : (0:ℝ) < |(a.center:ℝ)| := by exact_mod_cast lt_of_le_of_lt ha.1 hs'
  have hr : (a.radius:ℝ) < |(a.center:ℝ)| := by exact_mod_cast hs'
  have hx : |(a.center:ℝ)|-(a.radius:ℝ) ≤ |x| := by
    have hh := abs_sub_abs_le_abs_sub (a.center:ℝ) x
    rw [abs_sub_comm] at hh
    linarith [ha.2]
  have hxpos : 0 < |x| := lt_of_lt_of_le (sub_pos.mpr hr) hx
  refine ⟨div_nonneg ha.1 (mul_nonneg (abs_nonneg _) (sub_nonneg.mpr hs'.le)),?_⟩
  simp only [inv,Rat.cast_inv,Rat.cast_div,Rat.cast_mul,Rat.cast_sub,Rat.cast_abs]
  rw [inv_sub_inv (abs_pos.mp hxpos) (abs_pos.mp hc),abs_div,abs_mul,abs_sub_comm]
  apply (div_le_div₀ (by exact_mod_cast ha.1) ha.2 (mul_pos hc (sub_pos.mpr hr)) ?_)
  nlinarith [mul_le_mul_of_nonneg_right hx hc.le]

theorem certifies_flat (p : Poly) {a : Ball} {x : ℝ} (ha : a.Certifies x) (k : ℕ) :
    (a.flat p k).Certifies (Effective.flat p x) := by
  have hb := flatRound_certifies p a.center k
  refine ⟨add_nonneg hb.1 (mul_nonneg (polyBound_nonneg _) ha.1),?_⟩
  simp only [flat,Rat.cast_add,Rat.cast_mul]
  have hh := abs_sub_le (Effective.flat p x) (Effective.flat p (a.center:ℝ))
    ((flatRound p a.center k).center:ℝ)
  have hB : (0:ℝ) ≤ (polyBound (nextPoly p):ℝ) := by exact_mod_cast polyBound_nonneg _
  have hL := (flat_lipschitz p x (a.center:ℝ)).trans (mul_le_mul_of_nonneg_left ha.2 hB)
  linarith [hb.2]

def Converges (a : ℕ → Ball) (x : ℝ) : Prop :=
  Tendsto (fun k => (a k).center.cast) atTop (𝓝 x) ∧
  Tendsto (fun k => (a k).radius.cast) atTop (𝓝 (0:ℝ))

theorem converges_atom (q : ℚ) : Converges (fun _ => atom q) (q:ℝ) :=
  ⟨tendsto_const_nhds,by simp [atom]⟩

end VelocityDetection.Effective.Ball
end

end OAI
