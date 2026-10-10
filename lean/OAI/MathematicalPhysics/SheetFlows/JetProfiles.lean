import Mathlib
import OAI.MathematicalPhysics.SheetFlows.Clocks
import OAI.MathematicalPhysics.SheetFlows.JetCalculus

namespace OAI

/-! SheetFlows jet profiles. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology Polynomial
namespace Solenoidal
namespace JetExpr

def transition : JetExpr := .mul (.flat 1) .reciprocal

@[simp] theorem transition_eval (x : ℝ) : transition.eval x = Real.smoothTransition x := by
  simp [transition, eval, flatJet, transitionReciprocal, Real.smoothTransition, div_eq_mul_inv]

def cutoff (h d : ℚ) : JetExpr :=
  .mul (.affine (2/d) (2*(h+d)/d) transition)
    (.affine (-2/d) (2*(h+d)/d) transition)

def linearCutoff (h d : ℚ) : JetExpr := .mul .id (cutoff h d)

@[simp] theorem cutoff_eval (h d : ℚ) (x : ℝ) :
    (cutoff h d).eval x = plateau h d x := by
  simp only [cutoff, eval, transition_eval, plateau, Rat.cast_div, Rat.cast_mul,
    Rat.cast_add, Rat.cast_neg, Rat.cast_ofNat]
  congr 2 <;> ring

@[simp] theorem linearCutoff_eval (h d : ℚ) (x : ℝ) :
    (linearCutoff h d).eval x = linearProfile h d x := by
  simp [linearCutoff, eval, linearProfile]

def shiftedC (h d c : ℚ) : JetExpr := .affine 1 (-c) (cutoff h d)
def shiftedD (h d c : ℚ) : JetExpr := .affine 1 (-c) (linearCutoff h d)

def clock (a b : ℚ) : JetExpr := .affine (1/(b-a)) (-a/(b-a)) transition

def clockPulse (a b : ℚ) : JetExpr := (clock a b).diff

@[simp] theorem shiftedC_eval (h d c : ℚ) (x : ℝ) :
    (shiftedC h d c).eval x = plateau h d (x-c) := by
  simp [shiftedC, eval, sub_eq_add_neg]

@[simp] theorem shiftedD_eval (h d c : ℚ) (x : ℝ) :
    (shiftedD h d c).eval x = linearProfile h d (x-c) := by
  simp [shiftedD, eval, sub_eq_add_neg]

@[simp] theorem clock_eval (a b : ℚ) (x : ℝ) :
    (clock a b).eval x = pulseClock a b x := by
  simp only [clock, eval, transition_eval, pulseClock, Rat.cast_div, Rat.cast_one,
    Rat.cast_neg, Rat.cast_sub]
  congr 1
  ring

@[simp] theorem clockPulse_eval (a b : ℚ) (x : ℝ) :
    (clockPulse a b).eval x = localPulse a b x := by
  rw [clockPulse, ((clock a b).diff_correct x).deriv.symm]
  congr 1
  ext t
  exact clock_eval a b t

end JetExpr

theorem iteratedDeriv_eqOn_Icc {f g : ℝ → ℝ} {a b : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hab : a < b) (he : Set.EqOn f g (Set.Icc a b)) (n : ℕ) :
    Set.EqOn (iteratedDeriv n f) (iteratedDeriv n g) (Set.Icc a b) := by
  induction n with
  | zero => exact he
  | succ n ih =>
      intro x hx
      have hxs := uniqueDiffOn_Icc hab x hx
      have hfn := (hf.differentiable_iteratedDeriv n (by exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)) x).hasDerivAt.hasDerivWithinAt
        (s := Set.Icc a b)
      have hgn := (hg.differentiable_iteratedDeriv n (by exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)) x).hasDerivAt.hasDerivWithinAt
        (s := Set.Icc a b)
      have hfn' := hfn.congr (fun y hy => (ih hy).symm) (ih hx).symm
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      exact (hfn'.derivWithin hxs).symm.trans (hgn.derivWithin hxs)

theorem iteratedDeriv_periodic {f : ℝ → ℝ} {T : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : Function.Periodic f T) (n : ℕ) :
    Function.Periodic (iteratedDeriv n f) T := by
  induction n with
  | zero => exact hp
  | succ n ih =>
      intro x
      have hd := (hf.differentiable_iteratedDeriv n (by exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)) (x+T)).hasDerivAt
      have hc := hd.comp x ((hasDerivAt_id x).add_const T)
      have he : (fun y => iteratedDeriv n f (y+T)) = iteratedDeriv n f := funext ih
      change HasDerivAt (fun y => iteratedDeriv n f (y+T))
        (deriv (iteratedDeriv n f) (x+T)*1) x at hc
      rw [he, mul_one] at hc
      simpa only [iteratedDeriv_succ] using hc.deriv.symm

structure PeriodicJet (T : ℚ) (f : ℝ → ℝ) where
  positive : 0 < T
  smooth : ContDiff ℝ (⊤ : ℕ∞) f
  periodic : Function.Periodic f T
  expression : JetExpr
  on_chart : Set.EqOn f expression.eval (Set.Icc 0 T)

namespace PeriodicJet

variable {T : ℚ} {f : ℝ → ℝ}

def bound (p : PeriodicJet T f) (n : ℕ) : ℚ := (p.expression.nth n).bound T

theorem bound_nonneg (p : PeriodicJet T f) (n : ℕ) : 0 ≤ p.bound n :=
  JetExpr.bound_nonneg _ _

theorem derivative_on_chart (p : PeriodicJet T f) (n : ℕ) :
    Set.EqOn (iteratedDeriv n f) (p.expression.nth n).eval (Set.Icc 0 T) := by
  rw [JetExpr.nth_correct]
  exact iteratedDeriv_eqOn_Icc p.smooth p.expression.smooth (by exact_mod_cast p.positive)
    p.on_chart n

theorem bound_correct (p : PeriodicJet T f) (n : ℕ) (x : ℝ) :
    |iteratedDeriv n f x| ≤ (p.bound n : ℝ) := by
  have hT : (0:ℝ) < T := by exact_mod_cast p.positive
  let r : ℝ := (T:ℝ) * Int.fract (x/T)
  have hr : r ∈ Set.Icc (0:ℝ) (T:ℝ) := by
    constructor
    · exact mul_nonneg hT.le (Int.fract_nonneg _)
    · exact (mul_le_mul_of_nonneg_left (Int.fract_lt_one _).le hT.le).trans_eq (mul_one _)
  have he : r = x - (⌊x/(T:ℝ)⌋ : ℝ)*(T:ℝ) := by
    change (T:ℝ) * Int.fract (x/(T:ℝ)) = _
    rw [Int.fract, mul_sub]
    field_simp
  have hp := ((iteratedDeriv_periodic p.smooth p.periodic n).int_mul ⌊x/(T:ℝ)⌋).sub_eq x
  rw [← hp, ← he, p.derivative_on_chart n hr]
  apply JetExpr.bound_correct
  rw [abs_of_nonneg hr.1, abs_of_pos hT]
  exact hr.2

def ofPeriodize (T : ℚ) (hT : 0 < T) (e : JetExpr)
    (hz : ∀ x : ℝ, x ≤ 0 ∨ (T:ℝ) ≤ x → e.eval x = 0) :
    PeriodicJet T (periodize T e.eval) where
  positive := hT
  smooth := periodize_contDiff (by exact_mod_cast hT) (a := 0) (b := T)
    (e.eval)
    (by intro x hx; exact hz x (hx.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le))) e.smooth
  periodic := periodize_periodic _ _
  expression := e
  on_chart := fun _ hx => periodize_on_chart (by exact_mod_cast hT) _ hz hx

def const (T : ℚ) (hT : 0 < T) (q : ℚ) : PeriodicJet T (fun _ => (q:ℝ)) where
  positive := hT
  smooth := contDiff_const
  periodic := fun _ => rfl
  expression := .const q
  on_chart := fun _ _ => rfl

def add {g : ℝ → ℝ} (p : PeriodicJet T f) (q : PeriodicJet T g) :
    PeriodicJet T (fun x => f x + g x) where
  positive := p.positive
  smooth := p.smooth.add q.smooth
  periodic := p.periodic.add q.periodic
  expression := .add p.expression q.expression
  on_chart := by intro x hx; simp only [JetExpr.eval, p.on_chart hx, q.on_chart hx]

def mul {g : ℝ → ℝ} (p : PeriodicJet T f) (q : PeriodicJet T g) :
    PeriodicJet T (fun x => f x * g x) where
  positive := p.positive
  smooth := p.smooth.mul q.smooth
  periodic := p.periodic.mul q.periodic
  expression := .mul p.expression q.expression
  on_chart := by intro x hx; simp only [JetExpr.eval, p.on_chart hx, q.on_chart hx]

end PeriodicJet

def Cprofile_jet (h d c : ℚ) (hd : 0 < d) (hl : h+d ≤ c) (hu : c+(h+d) ≤ 10) :
    PeriodicJet 10 (Cprofile h d c) where
  positive := by norm_num
  smooth := Cprofile_contDiff _ _ (by exact_mod_cast hd)
  periodic := Cprofile_periodic _ _ _
  expression := JetExpr.shiftedC h d c
  on_chart := by
    intro x hx
    rw [JetExpr.shiftedC_eval]
    apply periodize_on_chart (by norm_num) _ _ hx
    apply shifted_profile_zero_outside _ (fun s hs => plateau_zero (by exact_mod_cast hd) hs)
    · exact_mod_cast hl
    · exact_mod_cast hu

def Dprofile_jet (h d c : ℚ) (hd : 0 < d) (hl : h+d ≤ c) (hu : c+(h+d) ≤ 10) :
    PeriodicJet 10 (Dprofile h d c) where
  positive := by norm_num
  smooth := Dprofile_contDiff _ _ (by exact_mod_cast hd)
  periodic := Dprofile_periodic _ _ _
  expression := JetExpr.shiftedD h d c
  on_chart := by
    intro x hx
    rw [JetExpr.shiftedD_eval]
    apply periodize_on_chart (by norm_num) _ _ hx
    apply shifted_profile_zero_outside _ (fun s hs => linearProfile_zero (by exact_mod_cast hd) hs)
    · exact_mod_cast hl
    · exact_mod_cast hu

def periodicPulse_jet (a b : ℚ) (hab : a < b) (ha : 0 ≤ a) (hb : b ≤ 1) :
    PeriodicJet 1 (periodicPulse a b) where
  positive := by norm_num
  smooth := periodicPulse_contDiff (by exact_mod_cast hab)
  periodic := by simpa using periodicPulse_periodic (a:ℝ) (b:ℝ)
  expression := JetExpr.clockPulse a b
  on_chart := by
    intro x hx
    rw [JetExpr.clockPulse_eval]
    exact periodicPulse_on_chart (by exact_mod_cast hab) (by exact_mod_cast ha)
      (by exact_mod_cast hb) (by simpa using hx)

end Solenoidal
end

end OAI
