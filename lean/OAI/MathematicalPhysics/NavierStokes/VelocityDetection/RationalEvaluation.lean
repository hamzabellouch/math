import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SmoothExpressions

namespace OAI

noncomputable section
namespace VelocityDetection.Effective.Ball
open Set Filter Function
open scoped Topology

theorem converges_add {a b : ℕ → Ball} {x y : ℝ} (ha : Converges a x) (hb : Converges b y) :
    Converges (fun k => (a k).add (b k)) (x+y) := by
  constructor
  · simpa only [add,Rat.cast_add] using ha.1.add hb.1
  · simpa only [add,Rat.cast_add,zero_add] using ha.2.add hb.2

theorem converges_neg {a : ℕ → Ball} {x : ℝ} (ha : Converges a x) :
    Converges (fun k => (a k).neg) (-x) := by
  exact ⟨by simpa only [neg,Rat.cast_neg] using ha.1.neg,ha.2⟩

theorem converges_mul {a b : ℕ → Ball} {x y : ℝ} (ha : Converges a x) (hb : Converges b y) :
    Converges (fun k => (a k).mul (b k)) (x*y) := by
  constructor
  · simpa only [mul,Rat.cast_mul] using ha.1.mul hb.1
  · simpa only [mul,Rat.cast_mul,Rat.cast_add,Rat.cast_abs,mul_zero,zero_add] using
      ((ha.1.abs.mul hb.2).add (hb.1.abs.mul ha.2)).add (ha.2.mul hb.2)

theorem converges_inv {a : ℕ → Ball} {x : ℝ} (ha : Converges a x) (hx : x ≠ 0) :
    Converges (fun k => (a k).inv) x⁻¹ := by
  constructor
  · simpa only [inv,Rat.cast_inv] using ha.1.inv₀ hx
  · have h := ha.2.div (ha.1.abs.mul (ha.1.abs.sub ha.2))
      (by simpa using mul_ne_zero (abs_ne_zero.mpr hx) (abs_ne_zero.mpr hx))
    change Tendsto (fun k => ((a k).radius:ℝ) / (|((a k).center:ℝ)| *
      (|((a k).center:ℝ)| - ((a k).radius:ℝ)))) atTop (𝓝 (0/(|x| *(|x|-0)))) at h
    simpa only [inv,Rat.cast_div,Rat.cast_mul,Rat.cast_sub,Rat.cast_abs,zero_div] using h

theorem eventually_invSafe {a : ℕ → Ball} {x : ℝ} (ha : Converges a x) (hx : x ≠ 0) :
    ∀ᶠ k in atTop, (a k).invSafe = true := by
  have h := (ha.1.abs.sub ha.2).eventually_const_lt (show (0:ℝ) < |x|-0 by simpa using abs_pos.mpr hx)
  filter_upwards [h] with k hk
  simp only [invSafe,decide_eq_true_eq]
  have : (a k).radius.cast < |((a k).center:ℝ)| := by linarith
  exact_mod_cast this

theorem converges_flat (p : Poly) {a : ℕ → Ball} {x : ℝ} (ha : Converges a x) :
    Converges (fun k => (a k).flat p k) (Effective.flat p x) := by
  have hr := flatRound_radius_tendsto p ha.1
  have hf : Tendsto (fun k => Effective.flat p ((a k).center:ℝ)) atTop (𝓝 (Effective.flat p x)) :=
    (contDiff_flat p).continuous.continuousAt.tendsto.comp ha.1
  have hc : Tendsto (fun k => ((flatRound p (a k).center k).center:ℝ)) atTop (𝓝 (Effective.flat p x)) := by
    apply tendsto_of_tendsto_of_dist hf
    apply squeeze_zero (fun k => dist_nonneg) (fun k => ?_) hr
    simpa only [Real.dist_eq] using (flatRound_certifies p (a k).center k).2
  refine ⟨hc,?_⟩
  simpa only [flat,Rat.cast_add,Rat.cast_mul,mul_zero,zero_add] using
    (hr.add (ha.2.const_mul (polyBound (nextPoly p):ℝ)))

end VelocityDetection.Effective.Ball
end

noncomputable section
namespace VelocityDetection.Effective.Expr
open Set Filter Function
open scoped Topology
variable {n : ℕ}

def round (a : Fin n → Ball) (k : ℕ) : Expr n → Ball :=
  Expr.rec (motive := fun _ => Ball)
    Ball.atom a
    (fun _ _ e f => e.add f)
    (fun _ e => e.neg)
    (fun _ _ e f => e.mul f)
    (fun _ e => e.inv)
    (fun p _ e => e.flat p k)

def safe (a : Fin n → Ball) (k : ℕ) : Expr n → Bool :=
  Expr.rec (motive := fun _ => Bool)
    (fun _ => true) (fun _ => true)
    (fun _ _ e f => e && f)
    (fun _ e => e)
    (fun _ _ e f => e && f)
    (fun e safe_e => safe_e && (e.round a k).invSafe)
    (fun _ _ e => e)

theorem round_certifies (e : Expr n) {a : Fin n → Ball} {x : Fin n → ℝ}
    (ha : ∀ i, (a i).Certifies (x i)) (k : ℕ) (hs : e.safe a k = true) :
    (e.round a k).Certifies (e.eval x) := by
  induction e with
  | rat q => exact Ball.certifies_atom q
  | var i => exact ha i
  | add e f he hf => exact Ball.certifies_add (he (Bool.and_eq_true_iff.mp hs).1) (hf (Bool.and_eq_true_iff.mp hs).2)
  | neg e he => exact Ball.certifies_neg (he hs)
  | mul e f he hf => exact Ball.certifies_mul (he (Bool.and_eq_true_iff.mp hs).1) (hf (Bool.and_eq_true_iff.mp hs).2)
  | inv e he => exact Ball.certifies_inv (he (Bool.and_eq_true_iff.mp hs).1) (Bool.and_eq_true_iff.mp hs).2
  | flat p e he => exact Ball.certifies_flat p (he hs) k

theorem round_converges (e : Expr n) {a : ℕ → Fin n → Ball} {x : Fin n → ℝ}
    (ha : ∀ i, Ball.Converges (fun k => a k i) (x i)) (hv : e.Valid x) :
    Ball.Converges (fun k => e.round (a k) k) (e.eval x) ∧
      ∀ᶠ k in atTop, e.safe (a k) k = true := by
  induction e with
  | rat q => exact ⟨Ball.converges_atom q,Eventually.of_forall (fun _ => rfl)⟩
  | var i => exact ⟨ha i,Eventually.of_forall (fun _ => rfl)⟩
  | add e f he hf | mul e f he hf =>
    obtain ⟨hec,hes⟩ := he hv.1
    obtain ⟨hfc,hfs⟩ := hf hv.2
    constructor
    · first | exact Ball.converges_add hec hfc | exact Ball.converges_mul hec hfc
    · filter_upwards [hes,hfs] with k hk hk'
      exact Bool.and_eq_true_iff.mpr ⟨hk,hk'⟩
  | neg e he =>
    obtain ⟨hc,hs⟩ := he hv
    exact ⟨Ball.converges_neg hc,hs⟩
  | flat p e he =>
    obtain ⟨hc,hs⟩ := he hv
    exact ⟨Ball.converges_flat p hc,hs⟩
  | inv e he =>
    obtain ⟨hc,hs⟩ := he hv.1
    refine ⟨Ball.converges_inv hc hv.2,?_⟩
    filter_upwards [hs,Ball.eventually_invSafe hc hv.2] with k hk hk'
    exact Bool.and_eq_true_iff.mpr ⟨hk,hk'⟩

end VelocityDetection.Effective.Expr
end

noncomputable section
namespace VelocityDetection.Effective
open Set Filter Function
open scoped Topology

noncomputable def coordinateD {n : ℕ} (i : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  deriv (fun s => f (update x i s)) (x i)

noncomputable def mixedD {n : ℕ} : List (Fin n) → ((Fin n → ℝ) → ℝ) → (Fin n → ℝ) → ℝ
  | [], f => f
  | i::is, f => mixedD is (coordinateD i f)

theorem coordinateD_congr {n : ℕ} {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (h : f =ᶠ[𝓝 x] g) (i : Fin n) : coordinateD i f x = coordinateD i g x := by
  have hc : Continuous (fun s : ℝ => update x i s) := continuous_const.update i continuous_id
  have ht : Tendsto (fun s : ℝ => update x i s) (𝓝 (x i)) (𝓝 x) := by
    simpa only [update_eq_self] using hc.continuousAt.tendsto (x := x i)
  exact (h.comp_tendsto ht).deriv_eq

theorem mixedD_congr {n : ℕ} {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (h : f =ᶠ[𝓝 x] g) (is : List (Fin n)) : mixedD is f x = mixedD is g x := by
  induction is generalizing f g with
  | nil => exact h.self_of_nhds
  | cons i is ih =>
    apply ih
    exact h.eventually_nhds.mono (fun _ hy => coordinateD_congr hy i)

end VelocityDetection.Effective
end

noncomputable section
namespace VelocityDetection.Effective.Expr
open Set Filter Function
open scoped Topology
variable {n : ℕ}

theorem coordinateD_eval {x : Fin n → ℝ} (e : Expr n) (h : e.Valid x) (i : Fin n) :
    coordinateD i (fun y => e.eval y) x = (e.diff i).eval x :=
  (e.hasDerivAt_eval h i).deriv

theorem mixedD_eval {x : Fin n → ℝ} (e : Expr n) (h : e.Valid x) (is : List (Fin n)) :
    mixedD is (fun y => e.eval y) x = (e.jet is).eval x := by
  induction is generalizing e with
  | nil => rfl
  | cons i is ih =>
    change mixedD is (coordinateD i (fun y => e.eval y)) x = (jet is (e.diff i)).eval x
    rw [mixedD_congr ((e.valid_eventually h).mono (fun y hy => e.coordinateD_eval hy i)) is]
    exact ih _ (e.valid_diff h i)

end VelocityDetection.Effective.Expr
end

noncomputable section
namespace VelocityDetection.Effective
open Set Filter Function
open scoped Topology

def accuracy (k : ℕ) : ℚ := (1/2)^k

def Names {n : ℕ} (q : Fin n → ℕ → ℚ) (x : Fin n → ℝ) : Prop :=
  ∀ i k, |x i-(q i k:ℝ)| ≤ (accuracy k:ℝ)

def inputBall {n : ℕ} (q : Fin n → ℕ → ℚ) (k : ℕ) (i : Fin n) : Ball :=
  ⟨q i k,accuracy k⟩

theorem accuracy_nonneg (k : ℕ) : 0 ≤ accuracy k := by unfold accuracy; positivity

theorem accuracy_tendsto : Tendsto (fun k => (accuracy k:ℝ)) atTop (𝓝 0) := by
  simpa only [accuracy,Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1))

theorem inputBall_certifies {n : ℕ} {q : Fin n → ℕ → ℚ} {x : Fin n → ℝ}
    (hq : Names q x) (k : ℕ) (i : Fin n) : (inputBall q k i).Certifies (x i) :=
  ⟨accuracy_nonneg k,hq i k⟩

theorem inputBall_converges {n : ℕ} {q : Fin n → ℕ → ℚ} {x : Fin n → ℝ}
    (hq : Names q x) (i : Fin n) : Ball.Converges (fun k => inputBall q k i) (x i) := by
  refine ⟨?_,accuracy_tendsto⟩
  apply tendsto_of_tendsto_of_dist tendsto_const_nhds
  exact squeeze_zero (fun _ => dist_nonneg) (fun k => by simpa only [Real.dist_eq,inputBall] using hq i k)
    accuracy_tendsto

def trial {n : ℕ} (e : Expr n) (is : List (Fin n)) (q : Fin n → ℕ → ℚ)
    (ε : ℚ) (k : ℕ) : Option ℚ :=
  let d := e.jet is
  let a := inputBall q k
  if d.safe a k && decide ((d.round a k).radius ≤ ε) then some (d.round a k).center else none

theorem trial_correct {n : ℕ} (e : Expr n) (is : List (Fin n))
    {q : Fin n → ℕ → ℚ} {x : Fin n → ℝ} (hq : Names q x) (he : e.Valid x)
    (ε : ℚ) (k : ℕ) {r : ℚ} (h : trial e is q ε k = some r) :
    |mixedD is (fun y => e.eval y) x-(r:ℝ)| ≤ (ε:ℝ) := by
  dsimp only [trial] at h
  split_ifs at h with ht
  · have hh := Bool.and_eq_true_iff.mp ht
    have hp : ((e.jet is).round (inputBall q k) k).radius ≤ ε := of_decide_eq_true hh.2
    cases Option.some.inj h
    rw [e.mixedD_eval he is]
    exact ((e.jet is).round_certifies (inputBall_certifies hq k) k hh.1).2.trans
      (by exact_mod_cast hp)

theorem trial_terminates {n : ℕ} (e : Expr n) (is : List (Fin n))
    {q : Fin n → ℕ → ℚ} {x : Fin n → ℝ} (hq : Names q x) (he : e.Valid x)
    {ε : ℚ} (hε : 0 < ε) : ∃ k r, trial e is q ε k = some r := by
  obtain ⟨hc,hs⟩ := (e.jet is).round_converges (inputBall_converges hq) (e.valid_jet he is)
  have hh := hc.2.eventually_lt_const (show (0:ℝ) < (ε:ℝ) by exact_mod_cast hε)
  obtain ⟨k,hk,hke⟩ := (hs.and hh).exists
  refine ⟨k,((e.jet is).round (inputBall q k) k).center,?_⟩
  have hp : ((e.jet is).round (inputBall q k) k).radius ≤ ε := by exact_mod_cast hke.le
  simp only [trial,hk,decide_eq_true hp,Bool.true_and,ite_true]

end VelocityDetection.Effective
end

end OAI
