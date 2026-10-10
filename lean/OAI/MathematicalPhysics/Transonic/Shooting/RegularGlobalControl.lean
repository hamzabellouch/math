import OAI.MathematicalPhysics.Transonic.Core

namespace OAI

section

/-! Exact integer polynomial evaluation and interval control for the regular shooting ODE. -/
namespace SepticProfile.IntegerPolynomial
open Set
abbrev Poly := List ℤ

def add : Poly → Poly → Poly
  | [],q => q
  | p,[] => p
  | a::p,b::q => (a+b)::add p q

def scale (a : ℤ) : Poly → Poly
  | [] => []
  | b::p => (a*b)::scale a p
def sub (p q : Poly) : Poly := add p (scale (-1) q)
def mul : Poly → Poly → Poly
  | [],_ => []
  | a::p,q => add (scale a q) (0::mul p q)
def der : Poly → Poly
  | [] => []
  | _::p => add p (0::der p)
def sq (p : Poly) : Poly := mul p p

def eval : Poly → ℝ → ℝ
  | [],_ => 0
  | a::p,x => a+x*eval p x

def norm : Poly → ℤ
  | [] => 0
  | a::p => |a|+norm p

def head (p : Poly) : ℤ := p.headD 0

def tailNorm (p : Poly) : ℤ := norm p.tail

def Positive (p : Poly) : Prop := tailNorm p<head p
instance (p : Poly) : Decidable (Positive p) := inferInstanceAs (Decidable (tailNorm p<head p))

lemma eval_add (p q : Poly) (x : ℝ) : eval (add p q) x=eval p x+eval q x := by
  induction p generalizing q with
  | nil => simp [add,eval]
  | cons a p ih =>
    cases q with
    | nil => simp [add,eval]
    | cons b q => simp [add,eval,ih]; ring

lemma eval_scale (a : ℤ) (p : Poly) (x : ℝ) : eval (scale a p) x=a*eval p x := by
  induction p with
  | nil => simp [scale,eval]
  | cons b p ih => simp only [scale,eval,Int.cast_mul,ih]; ring

lemma eval_sub (p q : Poly) (x : ℝ) : eval (sub p q) x=eval p x-eval q x := by
  simp [sub,eval_add,eval_scale,sub_eq_add_neg]

lemma eval_mul (p q : Poly) (x : ℝ) : eval (mul p q) x=eval p x*eval q x := by
  induction p with
  | nil => simp [mul,eval]
  | cons a p ih => rw [mul,eval_add,eval_scale,eval,ih,eval]; simp only [Int.cast_zero]; ring

lemma eval_sq (p : Poly) (x : ℝ) : eval (sq p) x=(eval p x)^2 := by
  rw [sq,eval_mul,pow_two]

lemma hasDerivAt_eval (p : Poly) (x : ℝ) : HasDerivAt (eval p) (eval (der p) x) x := by
  induction p with
  | nil => simpa only [eval,der] using hasDerivAt_const x (0:ℝ)
  | cons a p ih =>
    have hh := (hasDerivAt_const x (a : ℝ)).add ((hasDerivAt_id x).mul ih)
    change HasDerivAt (fun y => (a : ℝ)+y*eval p y)
      (0+(1*eval p x+x*eval (der p) x)) x at hh
    change HasDerivAt (fun y => (a : ℝ)+y*eval p y)
      (eval (add p (0::der p)) x) x
    simpa only [zero_add,one_mul,eval_add,eval,Int.cast_zero] using hh

lemma contDiff_eval (p : Poly) {n : WithTop ℕ∞} : ContDiff ℝ n (eval p) := by
  induction p with
  | nil => exact contDiff_const
  | cons a p ih => exact contDiff_const.add (contDiff_id.mul ih)

lemma norm_nonneg (p : Poly) : 0≤norm p := by
  induction p <;> simp_all [norm]; positivity

lemma eval_abs_le (p : Poly) {x : ℝ} (hx : x ∈ Icc 0 1) : |eval p x|≤norm p := by
  induction p with
  | nil => simp [eval,norm]
  | cons a p ih =>
    rw [eval,norm,Int.cast_add,Int.cast_abs]
    calc
      _ ≤ |(a : ℝ)|+|x*eval p x| := abs_add_le _ _
      _ = |(a : ℝ)|+x*|eval p x| := by rw [abs_mul,abs_of_nonneg hx.1]
      _ ≤ |(a : ℝ)|+|eval p x| := add_le_add_right (mul_le_of_le_one_left (abs_nonneg _) hx.2) _
      _ ≤ _ := add_le_add_right ih _

lemma eval_deviation (p : Poly) {x : ℝ} (hx : x ∈ Icc 0 1) :
    |eval p x-head p|≤tailNorm p := by
  cases p with
  | nil => simp [eval,head,tailNorm,norm]
  | cons a p =>
    simp only [head,List.headD_cons,eval,add_sub_cancel_left,tailNorm,List.tail_cons]
    rw [abs_mul,abs_of_nonneg hx.1]
    have h := eval_abs_le p hx
    exact (mul_le_of_le_one_left (abs_nonneg _) hx.2).trans h

lemma eval_pos {p : Poly} (hp : Positive p) {x : ℝ} (hx : x ∈ Icc 0 1) : 0<eval p x := by
  have hd := (abs_le.mp (eval_deviation p hx)).1
  have hp' : (tailNorm p : ℝ)<head p := by exact_mod_cast hp
  linarith

lemma eval_bounds (p : Poly) {x : ℝ} (hx : x ∈ Icc 0 1) :
    ((head p-tailNorm p : ℤ) : ℝ)≤eval p x ∧ eval p x≤((head p+tailNorm p : ℤ) : ℝ) := by
  have hh := abs_le.mp (eval_deviation p hx)
  push_cast
  constructor <;> linarith

end SepticProfile.IntegerPolynomial

namespace SepticProfile.IntegerPolynomial
open Set

/-- Numerator after substituting `z=(Z-Hs)/R`, `u=P(s)/Q` in the
exact normalized source ODE. All arithmetic in certificates is integral. -/
def residual (S SN K KN R Q Z H : ℤ) (p : Poly) : Poly :=
  let z : Poly := [Z,-H]
  let v := sub [Q^2] (sq p)
  add (scale (5*K*Q) (mul (mul (mul z (sub [S*R^2] (scale SN (sq z)))) v) (der p)))
    (scale (H*S*R) (mul (sub [5*Q^2] (scale 3 (sq p)))
      (add (scale KN (mul z v)) (scale (3*K) (sub (scale (Q^2) z) (scale (R*Q) p))))))

def denom (sigma z u : ℝ) : ℝ := z*(1-sigma*z^2)*(1-u^2)
noncomputable def numer (kappa z u : ℝ) : ℝ := (1-3*u^2/5)*(kappa*z*(1-u^2)+3*(z-u))

noncomputable def coordinate (R Z H : ℤ) (s : ℝ) : ℝ := (Z-H*s)/R

noncomputable def velocity (Q : ℤ) (p : Poly) (s : ℝ) : ℝ := eval p s/Q

lemma eval_singleton (a : ℤ) (x : ℝ) : eval [a] x=a := by simp [eval]
lemma eval_linear (a b : ℤ) (x : ℝ) : eval [a,b] x=a+b*x := by simp [eval]; ring

lemma eval_residual (S SN K KN R Q Z H : ℤ) (p : Poly) (s : ℝ)
    (hS : S≠0) (hK : K≠0) (hR : R≠0) (hQ : Q≠0) :
    eval (residual S SN K KN R Q Z H p) s =
      5*K*S*R^3*Q^4 *
       (denom (SN/S) (coordinate R Z H s) (velocity Q p s)*(eval (der p) s/Q)
        +(H/R)*numer (KN/K) (coordinate R Z H s) (velocity Q p s)) := by
  have hs : (S : ℝ)≠0 := by exact_mod_cast hS
  have hk : (K : ℝ)≠0 := by exact_mod_cast hK
  have hr : (R : ℝ)≠0 := by exact_mod_cast hR
  have hq : (Q : ℝ)≠0 := by exact_mod_cast hQ
  simp only [residual,eval_add,eval_sub,eval_scale,eval_mul,eval_sq,
    eval_singleton,eval_linear,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,Int.cast_neg,
    denom,numer,coordinate,velocity]
  field_simp
  ring

lemma hasDerivAt_velocity (Q : ℤ) (p : Poly) (s : ℝ) :
    HasDerivAt (velocity Q p) (eval (der p) s/Q) s :=
  (hasDerivAt_eval p s).div_const Q

lemma residual_strict {S SN K KN R Q Z H : ℤ} (hS : 0<S) (hK : 0<K)
    (hR : 0<R) (hQ : 0<Q) {p : Poly} (hp : Positive (residual S SN K KN R Q Z H p))
    {s : ℝ} (hs : s ∈ Icc 0 1) :
    0 < denom (SN/S) (coordinate R Z H s) (velocity Q p s)*(eval (der p) s/Q)
      +(H/R)*numer (KN/K) (coordinate R Z H s) (velocity Q p s) := by
  have h := eval_pos hp hs
  rw [eval_residual S SN K KN R Q Z H p s (ne_of_gt hS) (ne_of_gt hK)
    (ne_of_gt hR) (ne_of_gt hQ)] at h
  have hs' : (0:ℝ)<S := by exact_mod_cast hS
  have hk' : (0:ℝ)<K := by exact_mod_cast hK
  have hr' : (0:ℝ)<R := by exact_mod_cast hR
  have hq' : (0:ℝ)<Q := by exact_mod_cast hQ
  exact (mul_pos_iff_of_pos_left (by positivity)).mp h

lemma residual_negative {S SN K KN R Q Z H : ℤ} (hS : 0<S) (hK : 0<K)
    (hR : 0<R) (hQ : 0<Q) {p : Poly}
    (hp : Positive (scale (-1) (residual S SN K KN R Q Z H p)))
    {s : ℝ} (hs : s ∈ Icc 0 1) :
    denom (SN/S) (coordinate R Z H s) (velocity Q p s)*(eval (der p) s/Q)
      +(H/R)*numer (KN/K) (coordinate R Z H s) (velocity Q p s) < 0 := by
  have h := eval_pos hp hs
  rw [eval_scale,eval_residual S SN K KN R Q Z H p s (ne_of_gt hS)
    (ne_of_gt hK) (ne_of_gt hR) (ne_of_gt hQ)] at h
  have hs' : (0:ℝ)<S := by exact_mod_cast hS
  have hk' : (0:ℝ)<K := by exact_mod_cast hK
  have hr' : (0:ℝ)<R := by exact_mod_cast hR
  have hq' : (0:ℝ)<Q := by exact_mod_cast hQ
  have hn : ((5:ℝ)*K*S*R^3*Q^4) *
        (denom (SN/S) (coordinate R Z H s) (velocity Q p s)*(eval (der p) s/Q)
        +(H/R)*numer (KN/K) (coordinate R Z H s) (velocity Q p s))<0 := by
    norm_num only [Int.cast_neg,Int.cast_one,neg_one_mul] at h
    linarith
  exact neg_pos.mp ((mul_pos_iff_of_pos_left (show (0:ℝ)<5*K*S*R^3*Q^4 by positivity)).mp (by nlinarith : 0<(5:ℝ)*K*S*R^3*Q^4 * -_))
end SepticProfile.IntegerPolynomial

namespace SepticProfile.IntegerPolynomial

@[simp] lemma eval_zero (p : Poly) : eval p 0=head p := by
  cases p <;> simp [eval,head]

@[simp] lemma eval_one (p : Poly) : eval p 1=(p.sum : ℤ) := by
  induction p <;> simp_all [eval]

structure Step where
  Z : ℤ
  H : ℤ
  lo : Poly
  hi : Poly

def Range (Q : ℤ) (p : Poly) : Prop :=
  0<head p-tailNorm p ∧ 1000*(head p+tailNorm p)<999*Q
instance (Q : ℤ) (p : Poly) : Decidable (Range Q p) :=
  inferInstanceAs (Decidable (_ ∧ _))

def Valid (S SN K KN R Q : ℤ) (a : Step) : Prop :=
  0<a.H ∧ 9*R≤10*(a.Z-a.H) ∧ 100*a.Z≤99*R ∧
  Range Q a.lo ∧ Range Q a.hi ∧ head a.lo≤head a.hi ∧
  Positive (scale (-1) (residual S SN K KN R Q a.Z a.H a.lo)) ∧
  Positive (residual S SN K KN R Q a.Z a.H a.hi)
instance (S SN K KN R Q : ℤ) (a : Step) : Decidable (Valid S SN K KN R Q a) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

lemma range_velocity {Q : ℤ} (hq : 0<Q) {p : Poly} (hp : Range Q p) {s : ℝ}
    (hs : s ∈ Set.Icc 0 1) : velocity Q p s ∈ Set.Icc (0:ℝ) (999/1000) := by
  have hq' : (0:ℝ)<Q := by exact_mod_cast hq
  have hr := eval_bounds p hs
  have hlo : (0:ℝ)<((head p-tailNorm p : ℤ) : ℝ) := by exact_mod_cast hp.1
  have hhi : (1000:ℝ)*((head p+tailNorm p : ℤ) : ℝ)<999*Q := by exact_mod_cast hp.2
  constructor
  · exact div_nonneg (le_of_lt (hlo.trans_le hr.1)) hq'.le
  · apply (div_le_iff₀ hq').mpr
    nlinarith

lemma coordinate_bounds {R Z H : ℤ} (hr : 0<R) (hh : 0<H)
    (hstart : 100*Z≤99*R) (hend : 9*R≤10*(Z-H)) {s : ℝ}
    (hs : s ∈ Set.Icc 0 1) : coordinate R Z H s ∈ Set.Icc (9/10:ℝ) (99/100) := by
  have hr' : (0:ℝ)<R := by exact_mod_cast hr
  have hh' : (0:ℝ)<H := by exact_mod_cast hh
  have ha : (100:ℝ)*Z≤99*R := by exact_mod_cast hstart
  have hb : (9:ℝ)*R≤10*(Z-H) := by exact_mod_cast hend
  unfold coordinate
  constructor
  · apply (le_div_iff₀ hr').mpr
    nlinarith [mul_le_of_le_one_right hh'.le hs.2]
  · apply (div_le_iff₀ hr').mpr
    nlinarith [mul_nonneg hh'.le hs.1]

lemma denom_pos {sigma z u : ℝ} (hsigma : sigma ∈ Set.Icc (0:ℝ) 1)
    (hz : z ∈ Set.Icc (9/10:ℝ) (99/100)) (hu : u ∈ Set.Icc (0:ℝ) (999/1000)) :
    0<denom sigma z u := by
  have hz0 : 0<z := by linarith [hz.1]
  have hz1 : z^2<1 := by nlinarith [hz.2]
  have hu1 : u^2<1 := by nlinarith [hu.1,hu.2]
  have hsz : sigma*z^2≤z^2 := mul_le_of_le_one_left (sq_nonneg _) hsigma.2
  exact mul_pos (mul_pos hz0 (by linarith)) (by linarith)
end SepticProfile.IntegerPolynomial


namespace SepticProfile.IntegerPolynomial
open Set
open RegularContinuation

noncomputable def stepField (sigma kappa : ℝ) (R Z H : ℤ) (s w : ℝ) : ℝ :=
  -(H/R)*numer kappa (coordinate R Z H s) (clamp 0 (999/1000) w)/
    denom sigma (coordinate R Z H s) (clamp 0 (999/1000) w)

/-- Exact signed polynomial residuals control the actual clamped ODE, not an
approximate trajectory. The comparison proves the clamp inactive on this step. -/
theorem step_control {S SN K KN R Q : ℤ} (hs : 0<S) (hk : 0<K) (hr : 0<R)
    (hq : 0<Q) (hsigma : ((SN:ℝ)/S) ∈ Icc (0:ℝ) 1) {a : Step}
    (ha : Valid S SN K KN R Q a) {w : ℝ → ℝ}
    (hwc : ContinuousOn w (Icc 0 1))
    (hwd : ∀ s ∈ Icc (0:ℝ) 1, HasDerivWithinAt w
      (stepField (SN/S) (KN/K) R a.Z a.H s (w s)) (Icc 0 1) s)
    (hw0 : w 0 ∈ Icc ((head a.lo:ℝ)/Q) ((head a.hi:ℝ)/Q)) :
    ∀ s ∈ Icc (0:ℝ) 1, w s ∈ Icc (velocity Q a.lo s) (velocity Q a.hi s) := by
  obtain ⟨hh,hend,hstart,hlo,hhi,_,hlor,_hhir⟩ := ha
  have hright (s : ℝ) (ht : s ∈ Ico (0:ℝ) 1) : HasDerivWithinAt w
      (stepField (SN/S) (KN/K) R a.Z a.H s (w s)) (Ici s) s := by
    apply (hwd s ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
  have hupper : ∀ s ∈ Icc (0:ℝ) 1, w s≤velocity Q a.hi s := by
    apply image_le_of_deriv_right_lt_deriv_boundary' hwc hright
      (B' := fun s => eval (der a.hi) s/Q) (by simpa [velocity] using hw0.2)
      (fun s _ => (hasDerivAt_velocity Q a.hi s).continuousAt.continuousWithinAt)
      (fun s _ => (hasDerivAt_velocity Q a.hi s).hasDerivWithinAt)
    intro s ht he
    have he2 : s ∈ Icc (0:ℝ) 1 := ⟨ht.1,ht.2.le⟩
    have hrange := range_velocity hq hhi he2
    have hz := coordinate_bounds hr hh hstart hend he2
    have hd := denom_pos hsigma hz hrange
    have heq := clamp_eq hrange
    have hhres := residual_strict hs hk hr hq _hhir he2
    dsimp only [stepField]
    rw [he,heq]
    apply (div_lt_iff₀ hd).mpr
    nlinarith
  have hlower : ∀ s ∈ Icc (0:ℝ) 1, velocity Q a.lo s≤w s := by
    have hhcmp := image_le_of_deriv_right_lt_deriv_boundary' hwc.neg
      (fun s hs => (hright s hs).neg) (B := fun s => -velocity Q a.lo s)
      (B' := fun s => -(eval (der a.lo) s/Q))
      (by simpa [velocity] using neg_le_neg hw0.1)
      (fun s _ => (hasDerivAt_velocity Q a.lo s).neg.continuousAt.continuousWithinAt)
      (fun s _ => (hasDerivAt_velocity Q a.lo s).neg.hasDerivWithinAt)
    have hhcmp' : ∀ s ∈ Icc (0:ℝ) 1, -w s≤ -velocity Q a.lo s := by
      apply hhcmp
      intro s ht he
      have he' : w s=velocity Q a.lo s := neg_inj.mp he
      have he2 : s ∈ Icc (0:ℝ) 1 := ⟨ht.1,ht.2.le⟩
      have hrange := range_velocity hq hlo he2
      have hz := coordinate_bounds hr hh hstart hend he2
      have hd := denom_pos hsigma hz hrange
      have heq := clamp_eq hrange
      have hlres := residual_negative hs hk hr hq hlor he2
      apply neg_lt_neg
      dsimp only [stepField]
      rw [he',heq]
      apply (lt_div_iff₀ hd).mpr
      nlinarith
    intro s hs
    linarith [hhcmp' s hs]
  intro s hs
  exact ⟨hlower s hs,hupper s hs⟩

end SepticProfile.IntegerPolynomial

namespace SepticProfile.IntegerPolynomial
open Set RegularContinuation

noncomputable def globalField (sigma kappa : ℝ) (t w : ℝ) : ℝ :=
  -numer kappa (99/100-t) (clamp 0 (999/1000) w)/
    denom sigma (99/100-t) (clamp 0 (999/1000) w)
noncomputable def stepTime (R Z H : ℤ) (s : ℝ) : ℝ := 99/100-coordinate R Z H s
noncomputable def startTime (R : ℤ) (a : Step) : ℝ := 99/100-a.Z/R
noncomputable def stopTime (R : ℤ) (a : Step) : ℝ := 99/100-((a.Z-a.H : ℤ):ℝ)/R

lemma hasDerivAt_stepTime (R Z H : ℤ) (s : ℝ) : HasDerivAt (stepTime R Z H) (H/R) s := by
  have hh := (hasDerivAt_const s (99/100:ℝ)).sub
    (((hasDerivAt_const s (Z:ℝ)).sub ((hasDerivAt_id s).const_mul (H:ℝ))).div_const R)
  change HasDerivAt (stepTime R Z H) (0-(0-(H:ℝ)*1)/R) s at hh
  simpa only [mul_one,zero_sub,neg_div,neg_neg] using hh

lemma stepTime_mem {R Z H : ℤ} (hr : 0<R) (hh : 0<H)
    (hstart : 100*Z≤99*R) (hend : 9*R≤10*(Z-H)) {s : ℝ}
    (hs : s ∈ Icc (0:ℝ) 1) : stepTime R Z H s ∈ Icc (0:ℝ) (9/100) := by
  have hz := coordinate_bounds hr hh hstart hend hs
  unfold stepTime
  constructor <;> linarith [hz.1,hz.2]

lemma localized_derivative {sigma kappa : ℝ} {R Z H : ℤ} (hr : 0<R) (hh : 0<H)
    (hstart : 100*Z≤99*R) (hend : 9*R≤10*(Z-H)) {u : ℝ → ℝ}
    (hud : ∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt u (globalField sigma kappa t (u t))
      (Icc 0 (9/100)) t) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    HasDerivWithinAt (u ∘ stepTime R Z H)
      (stepField sigma kappa R Z H s ((u ∘ stepTime R Z H) s)) (Icc 0 1) s := by
  have hm := stepTime_mem hr hh hstart hend hs
  have hd := (hud _ hm).comp s (hasDerivAt_stepTime R Z H s).hasDerivWithinAt
    (fun t ht => stepTime_mem hr hh hstart hend ht)
  have he : globalField sigma kappa (stepTime R Z H s) (u (stepTime R Z H s)) * (H/R) =
      stepField sigma kappa R Z H s ((u ∘ stepTime R Z H) s) := by
    dsimp [globalField,stepField,stepTime]
    simp only [sub_sub_cancel]
    ring
  rw [← he]
  exact hd

/-- Each integer certificate propagates a rigorous interval for the same
single globally constructed clamped solution. No approximate flow is used. -/
theorem global_step_endpoint {S SN K KN R Q : ℤ} (hs : 0<S) (hk : 0<K) (hr : 0<R)
    (hq : 0<Q) (hsigma : ((SN:ℝ)/S) ∈ Icc (0:ℝ) 1) {a : Step}
    (ha : Valid S SN K KN R Q a) {u : ℝ → ℝ}
    (hud : ∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt u (globalField (SN/S) (KN/K) t (u t))
      (Icc 0 (9/100)) t)
    (hu0 : u (startTime R a) ∈ Icc ((head a.lo:ℝ)/Q) ((head a.hi:ℝ)/Q)) :
    u (stopTime R a) ∈ Icc ((a.lo.sum:ℝ)/Q) ((a.hi.sum:ℝ)/Q) := by
  have hd := localized_derivative hr ha.1 ha.2.2.1 ha.2.1 hud
  have hc : ContinuousOn (u ∘ stepTime R a.Z a.H) (Icc 0 1) :=
    fun s hs => (hd s hs).continuousWithinAt
  have hzero : (u ∘ stepTime R a.Z a.H) 0=u (startTime R a) := by
    simp [stepTime,coordinate,startTime]
  have hb := step_control hs hk hr hq hsigma ha hc hd (hzero.symm ▸ hu0) 1 (by norm_num)
  simpa [stepTime,coordinate,stopTime,velocity] using hb

lemma join_bound {R Q : ℤ} (hq : 0<Q) {a b : Step} {u : ℝ → ℝ}
    (hjoin : a.Z-a.H=b.Z ∧ head b.lo≤a.lo.sum ∧ a.hi.sum≤head b.hi)
    (hb : u (stopTime R a) ∈ Icc ((a.lo.sum:ℝ)/Q) ((a.hi.sum:ℝ)/Q)) :
    u (startTime R b) ∈ Icc ((head b.lo:ℝ)/Q) ((head b.hi:ℝ)/Q) := by
  have he : stopTime R a=startTime R b := by rw [stopTime,startTime,hjoin.1]
  rw [he] at hb
  have hq' : (0:ℝ)≤Q := le_of_lt (by exact_mod_cast hq)
  constructor
  · exact (div_le_div_of_nonneg_right (by exact_mod_cast hjoin.2.1) hq').trans hb.1
  · exact hb.2.trans (div_le_div_of_nonneg_right (by exact_mod_cast hjoin.2.2) hq')
end SepticProfile.IntegerPolynomial

namespace SepticProfile.IntegerPolynomial
open Set RegularContinuation

lemma regular_field_contDiffOn (sigma kappa : ℝ) (hs : sigma ∈ Icc (0:ℝ) 1) :
    ContDiffOn ℝ 1 (fun p : ℝ×ℝ => -numer kappa (99/100-p.1) p.2 /
      denom sigma (99/100-p.1) p.2) (Icc (0:ℝ) (9/100) ×ˢ Icc (0:ℝ) (999/1000)) := by
  apply ContDiffOn.div
  · unfold numer
    fun_prop
  · unfold denom
    fun_prop
  · intro p hp
    apply ne_of_gt (denom_pos hs _ hp.2)
    constructor <;> linarith [hp.1.1,hp.1.2]

/-- A single exact clamped trajectory exists on the entire regular shooting
interval. Step certificates will certify its value, rather than assume a flow. -/
theorem exists_global_clamped_solution (sigma kappa : ℝ) (hs : sigma ∈ Icc (0:ℝ) 1)
    (u0 : ℝ) : ∃ u : ℝ → ℝ, u 0=u0 ∧ ContinuousOn u (Icc (0:ℝ) (9/100)) ∧
      ∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt u (globalField sigma kappa t (u t))
        (Icc 0 (9/100)) t := by
  exact exists_clamped_solution (by norm_num) (by norm_num)
    (regular_field_contDiffOn sigma kappa hs) u0
end SepticProfile.IntegerPolynomial


end

end OAI
