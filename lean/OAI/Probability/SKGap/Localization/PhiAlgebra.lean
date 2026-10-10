import Mathlib
import OAI.Probability.SKGap.Terminal.FiniteSpinCalculus
import OAI.Probability.SKGap.Localization.CoordinateDeriv
import OAI.Probability.SKGap.Gaussian.PhiMoments

namespace OAI

section

noncomputable section
namespace SKGap.Stein

inductive KernelExpr where
  | atom (p q : ℕ) (b : Bool)
  | add (f g : KernelExpr)
  | scale (c : ℝ) (f : KernelExpr)
  | tz (f : KernelExpr)
  | tr (f : KernelExpr)

namespace KernelExpr

def eval : KernelExpr → ℝ → ℝ → ℝ → ℝ
  | atom p q b,z,r,a  =>  moment p q b z r a
  | add f g,z,r,a  =>  eval f z r a+eval g z r a
  | scale c f,z,r,a  =>  c*eval f z r a
  | tz f,z,r,a  =>  Real.tanh z*eval f z r a
  | tr f,z,r,a  =>  Real.tanh r*eval f z r a

def mass : KernelExpr → ℝ
  | atom _ _ _  =>  1
  | add f g  =>  mass f+mass g
  | scale c f  =>  |c| *mass f
  | tz f  =>  mass f
  | tr f  =>  mass f

lemma mass_nonneg (f : KernelExpr) : 0 ≤ mass f := by
  induction f <;> simp only [mass] <;> positivity

lemma relative_bound (f : KernelExpr) (z r a : ℝ) : |eval f z r a| ≤ mass f*phi z r a := by
  induction f with
  | atom p q b  =>  simpa only [eval,mass,one_mul] using moment_relative_bound p q b z r a
  | add f g hf hg  =>
    exact (abs_add_le _ _).trans (by simpa only [eval,mass,add_mul] using add_le_add hf hg)
  | scale c f hf  =>
    dsimp only [eval,mass]
    rw [abs_mul,mul_assoc]
    exact mul_le_mul_of_nonneg_left hf (abs_nonneg c)
  | tz f hf  =>
    dsimp only [eval,mass]
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (Real.abs_tanh_lt_one z).le (abs_nonneg _)).trans
      (by simpa only [one_mul] using hf)
  | tr f hf  =>
    dsimp only [eval,mass]
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (Real.abs_tanh_lt_one r).le (abs_nonneg _)).trans
      (by simpa only [one_mul] using hf)

def dz : KernelExpr → KernelExpr
  | atom p q b  =>  add (atom (p+1) q (!b)) (scale (-1) (tz (atom p q b)))
  | add f g  =>  add (dz f) (dz g)
  | scale c f  =>  scale c (dz f)
  | tz f  =>  add (add f (scale (-1) (tz (tz f)))) (tz (dz f))
  | tr f  =>  tr (dz f)

def dr : KernelExpr → KernelExpr
  | atom p q b  =>  add (scale (-1) (atom (p+1) q (!b))) (scale (-1) (tr (atom p q b)))
  | add f g  =>  add (dr f) (dr g)
  | scale c f  =>  scale c (dr f)
  | tz f  =>  tz (dr f)
  | tr f  =>  add (add f (scale (-1) (tr (tr f)))) (tr (dr f))

def da : KernelExpr → KernelExpr
  | atom p q b  =>  atom p (q+1) b
  | add f g  =>  add (da f) (da g)
  | scale c f  =>  scale c (da f)
  | tz f  =>  tz (da f)
  | tr f  =>  tr (da f)

lemma hasDerivAt_z (f : KernelExpr) (z r a : ℝ) :
    HasDerivAt (fun z => eval f z r a) (eval (dz f) z r a) z := by
  induction f with
  | atom p q b  =>  simpa only [eval,dz,neg_mul,one_mul,←sub_eq_add_neg] using moment_hasDerivAt_z p q b z r a
  | add f g hf hg  =>  exact hf.add hg
  | scale c f hf  =>  exact hf.const_mul c
  | tz f hf  =>
    convert! (SKGapCutoff.tanh_hasDerivAt z).mul hf using 1
    dsimp only [eval,dz,SKGapCutoff.scalarVariance]
    ring
  | tr f hf  =>  exact hf.const_mul _

lemma hasDerivAt_r (f : KernelExpr) (z r a : ℝ) :
    HasDerivAt (fun r => eval f z r a) (eval (dr f) z r a) r := by
  induction f with
  | atom p q b  =>  simpa only [eval,dr,neg_mul,one_mul,←sub_eq_add_neg] using moment_hasDerivAt_r p q b z r a
  | add f g hf hg  =>  exact hf.add hg
  | scale c f hf  =>  exact hf.const_mul c
  | tz f hf  =>  exact hf.const_mul _
  | tr f hf  =>
    convert! (SKGapCutoff.tanh_hasDerivAt r).mul hf using 1
    dsimp only [eval,dr,SKGapCutoff.scalarVariance]
    ring

lemma hasDerivAt_a (f : KernelExpr) (z r a : ℝ) :
    HasDerivAt (fun a => eval f z r a) (eval (da f) z r a) a := by
  induction f with
  | atom p q b  =>  exact moment_hasDerivAt_a p q b z r a
  | add f g hf hg  =>  exact hf.add hg
  | scale c f hf  =>  exact hf.const_mul c
  | tz f hf  =>  exact hf.const_mul _
  | tr f hf  =>  exact hf.const_mul _

end KernelExpr

inductive Axis where | z | r | a

def coordinateDeriv (i : Axis) (F : ℝ→ℝ→ℝ→ℝ) : ℝ→ℝ→ℝ→ℝ := match i with
  | .z  =>  fun z r a => deriv (fun z => F z r a) z
  | .r  =>  fun z r a => deriv (fun r => F z r a) r
  | .a  =>  fun z r a => deriv (fun a => F z r a) a

def mixed (l : List Axis) (F : ℝ→ℝ→ℝ→ℝ) : ℝ→ℝ→ℝ→ℝ := match l with
  | []  =>  F
  | i::l  =>  coordinateDeriv i (mixed l F)

namespace KernelExpr

def d (i : Axis) : KernelExpr → KernelExpr := match i with
  | .z  =>  dz | .r  =>  dr | .a  =>  da

def mixedExpr (l : List Axis) (f : KernelExpr) : KernelExpr := match l with
  | []  =>  f
  | i::l  =>  d i (mixedExpr l f)

lemma partial_eval (i : Axis) (f : KernelExpr) : coordinateDeriv i (eval f)=eval (d i f) := by
  funext z r a
  cases i with
  | z  =>  exact (hasDerivAt_z f z r a).deriv
  | r  =>  exact (hasDerivAt_r f z r a).deriv
  | a  =>  exact (hasDerivAt_a f z r a).deriv

lemma mixed_eval (l : List Axis) (f : KernelExpr) : mixed l (eval f)=eval (mixedExpr l f) := by
  induction l with
  | nil  =>  rfl
  | cons i l ih  =>  rw [mixed,ih,partial_eval]; rfl

theorem all_mixed_relative_bound (l : List Axis) (z r a : ℝ) :
    |mixed l phi z r a| ≤ mass (mixedExpr l (atom 0 0 false))*phi z r a := by
  have he : phi=eval (atom 0 0 false) := funext fun z => funext fun r => funext fun a => (moment_base z r a).symm
  rw [he,mixed_eval]
  simpa only [eval,moment_base] using relative_bound (mixedExpr l (atom 0 0 false)) z r a

end KernelExpr
end SKGap.Stein

end
end

end OAI
