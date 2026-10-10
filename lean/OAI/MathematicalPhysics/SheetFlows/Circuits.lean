import Mathlib
import OAI.MathematicalPhysics.SheetFlows.RationalFormula
import OAI.MathematicalPhysics.SheetFlows.Computing

namespace OAI

/-! SheetFlows circuits. -/

section
open Set Filter Encodable Denumerable
open scoped BigOperators Topology Polynomial
namespace Solenoidal

noncomputable def flatMono (n : ℕ) : ℝ → ℝ := flatJet (Polynomial.X^n)

theorem flatJet_sub (p q : ℚ[X]) : flatJet (p-q) = flatJet p - flatJet q := by
  funext x
  simp [flatJet,sub_mul]

theorem flatJet_C_mul (a : ℚ) (p : ℚ[X]) :
    flatJet (Polynomial.C a*p) = fun x => (a:ℝ)*flatJet p x := by
  funext x
  simp [flatJet,mul_assoc]

theorem flatMono_deriv (n : ℕ) (x : ℝ) :
    HasDerivAt (flatMono n) (flatMono (n+2) x - (n:ℝ)*flatMono (n+1) x) x := by
  have hp : flatNext (Polynomial.X^n) =
      Polynomial.X^(n+2) - Polynomial.C (n:ℚ)*Polynomial.X^(n+1) := by
    cases n with
    | zero => simp [flatNext]
    | succ n =>
      rw [flatNext, Polynomial.derivative_X_pow]
      simp only [Nat.add_sub_cancel, pow_succ]
      ring
  have h := flatJet_hasDerivAt (Polynomial.X^n) x
  rw [hp,flatJet_sub,flatJet_C_mul] at h
  simpa [flatMono] using h

theorem flatMono_bound (n : ℕ) (x : ℝ) : |flatMono n x| ≤ (n.factorial:ℝ) := by
  have h : flatBound (Polynomial.X^n) = (n.factorial:ℚ) := by simp [flatBound, Polynomial.support_X_pow]
  simpa only [flatMono, h, Rat.cast_natCast] using flatJet_bound (Polynomial.X^n) x

abbrev Atom := Fin 4 × ℚ × ℚ × ℕ

namespace Atom

def argument (a : Atom) (q : Fin 4 → ℚ) : ℚ := a.2.1*q a.1+a.2.2.1

noncomputable def profile (k : ℕ) : ℝ → ℝ :=
  if k=0 then id else if k=1 then transitionReciprocal else flatMono (k-2)

noncomputable def eval (a : Atom) (z : SpaceTime) : ℝ :=
  profile a.2.2.2 ((a.2.1:ℝ)*coordinateLinear a.1 z+a.2.2.1)

def approx (a : Atom) (q : Fin 4 → ℚ) (n : ℕ) : QBall :=
  if a.2.2.2=0 then QBall.point (argument a q)
  else if a.2.2.2=1 then QBall.reciprocalApprox (argument a q) n
  else QBall.flatApprox (a.2.2.2-2) (argument a q) n

def bound (a : Atom) (R : ℚ) : ℚ :=
  if a.2.2.2=0 then |a.2.1| * |R| + |a.2.2.1|
  else if a.2.2.2=1 then 16 else ((a.2.2.2-2).factorial:ℚ)

theorem profile_smooth (k : ℕ) : ContDiff ℝ (⊤:ℕ∞) (profile k) := by
  unfold profile
  split
  · exact contDiff_id
  · split
    · exact transitionReciprocal_smooth
    · exact flatJet_smooth _

theorem smooth (a : Atom) : ContDiff ℝ (⊤:ℕ∞) a.eval :=
  (profile_smooth _).comp
    ((contDiff_const.mul (coordinateLinear a.1).contDiff).add contDiff_const)

theorem bound_nonneg (a : Atom) (R : ℚ) : 0 ≤ a.bound R := by
  unfold bound
  split
  · positivity
  · split <;> positivity

theorem bound_correct (a : Atom) (R : ℚ) (z : SpaceTime)
    (hz : ∀ j, |coordinateLinear j z| ≤ |(R:ℝ)|) :
    |a.eval z| ≤ (a.bound R:ℝ) := by
  unfold eval profile bound
  split
  · simp only [id_eq,Rat.cast_add,Rat.cast_mul,Rat.cast_abs]
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (hz a.1) (abs_nonneg _)) le_rfl
  · split
    · exact transitionReciprocal_bound _
    · simpa using flatMono_bound _ _

end Atom

abbrev Circuit := Nat.Partrec.Code

namespace Circuit

open Nat.Partrec

def data {α : Type*} [Primcodable α] [Inhabited α] (c : Code) : α :=
  (decode (encode c)).getD default

def const (q : ℚ) : Circuit := Code.rfind' (ofNat Code (encode q))
def atom (a : Atom) : Circuit := Code.prec (ofNat Code (encode a)) Code.zero
abbrev add := Code.pair
abbrev mul := Code.comp

def sub (a b : Circuit) : Circuit := add a (mul (const (-1)) b)

noncomputable def eval : Circuit → SpaceTime → ℝ
  | .zero | .succ | .left | .right => fun _ => 0
  | .pair f g => fun z => eval f z + eval g z
  | .comp f g => fun z => eval f z * eval g z
  | .prec a _ => Atom.eval (data a) 
  | .rfind' a => fun _ => (data a : ℚ)

def approx : Circuit → (Fin 4 → ℚ) → ℕ → QBall
  | .zero | .succ | .left | .right => fun _ _ => QBall.point 0
  | .pair f g => fun q n => QBall.add (approx f q n) (approx g q n)
  | .comp f g => fun q n => QBall.mul (approx f q n) (approx g q n)
  | .prec a _ => Atom.approx (data a)
  | .rfind' a => fun _ _ => QBall.point (data a : ℚ)

def bound : Circuit → ℚ → ℚ
  | .zero | .succ | .left | .right => fun _ => 0
  | .pair f g => fun R => bound f R + bound g R
  | .comp f g => fun R => bound f R * bound g R
  | .prec a _ => Atom.bound (data a)
  | .rfind' a => fun _ => |(data a:ℚ)|

@[simp] theorem data_ofNat_encode {α : Type*} [Primcodable α] [Inhabited α] (a : α) :
    data (ofNat Code (encode a)) = a := by
  simp [data]

@[simp] theorem eval_const (q : ℚ) (z : SpaceTime) : eval (const q) z = q := by
  exact congrArg (fun q : ℚ => (q:ℝ)) (data_ofNat_encode q)
@[simp] theorem eval_atom (a : Atom) (z : SpaceTime) : eval (atom a) z = Atom.eval a z := by
  exact congrArg (fun a => Atom.eval a z) (data_ofNat_encode a)
@[simp] theorem eval_sub (a b : Circuit) (z : SpaceTime) :
    eval (sub a b) z = eval a z - eval b z := by simp [sub,add,mul,eval,sub_eq_add_neg]

theorem smooth (e : Circuit) : ContDiff ℝ (⊤:ℕ∞) (eval e) := by
  induction e with
  | zero | succ | left | right => exact contDiff_const
  | pair a b ha hb => exact ha.add hb
  | comp a b ha hb => exact ha.mul hb
  | prec a b ha hb => exact Atom.smooth _
  | rfind' a ha => exact contDiff_const

theorem bound_nonneg (e : Circuit) (R : ℚ) : 0 ≤ bound e R := by
  induction e with
  | zero | succ | left | right => exact le_rfl
  | pair a b ha hb => exact add_nonneg ha hb
  | comp a b ha hb => exact mul_nonneg ha hb
  | prec a b ha hb => exact Atom.bound_nonneg _ _
  | rfind' a ha => exact abs_nonneg _

theorem bound_correct (e : Circuit) (R : ℚ) (z : SpaceTime)
    (hz : ∀ j, |coordinateLinear j z| ≤ |(R:ℝ)|) :
    |(eval e) z| ≤ (bound e R:ℝ) := by
  induction e with
  | zero | succ | left | right => simp [eval,bound]
  | pair a b ha hb =>
    simpa [eval,bound] using (abs_add_le (eval a z) (eval b z)).trans (add_le_add ha hb)
  | comp a b ha hb =>
    have h := mul_le_mul ha hb (abs_nonneg _) (by exact_mod_cast bound_nonneg a R)
    simpa [eval,bound,abs_mul] using h
  | prec a b ha hb => exact Atom.bound_correct _ _ _ hz
  | rfind' a ha => simp [eval,bound]

def ofRational (q : Fin 4 → ℚ) : SpaceTime :=
  (q 0, ![(q 1:ℝ),q 2,q 3])

@[simp] theorem coordinate_ofRational (q : Fin 4 → ℚ) (j : Fin 4) :
    coordinateLinear j (ofRational q) = (q j:ℝ) := by fin_cases j <;> rfl

@[simp] theorem flatten_ofRational (q : Fin 4 → ℚ) (j : Fin 4) :
    flatten (ofRational q) j = (q j:ℝ) := by fin_cases j <;> rfl

theorem atom_approximates (a : Atom) (q : Fin 4 → ℚ) :
    QBall.Approximates (a.approx q) (a.eval (ofRational q)) := by
  unfold Atom.approx
  split
  · rename_i h
    simpa [Atom.eval,Atom.profile,Atom.argument, coordinate_ofRational,h] using QBall.approximates_point (a.argument q)
  · split
    · rename_i h h1
      simpa [Atom.eval,Atom.profile,Atom.argument, coordinate_ofRational,h,h1] using QBall.reciprocalApprox_approximates (a.argument q)
    · rename_i h h1
      simpa [Atom.eval,Atom.profile,Atom.argument, coordinate_ofRational,flatMono,h,h1] using
        QBall.flatApprox_approximates (a.2.2.2-2) (a.argument q)

theorem approximates (e : Circuit) (q : Fin 4 → ℚ) :
    QBall.Approximates (e.approx q) ((eval e) (ofRational q)) := by
  induction e with
  | zero | succ | left | right => simpa [approx,eval] using QBall.approximates_point 0
  | pair a b ha hb => exact ha.add hb
  | comp a b ha hb => exact ha.mul hb
  | prec a b ha hb => exact atom_approximates _ _
  | rfind' a ha => exact QBall.approximates_point _

end Circuit
end Solenoidal
end

open Set Filter Encodable Denumerable
open scoped BigOperators Topology Polynomial
namespace Solenoidal
namespace Atom

noncomputable def profileDerivative (k : ℕ) (x : ℝ) : ℝ :=
  if k=0 then 1 else if k=1 then
    -(transitionReciprocal x * transitionReciprocal x) * (flatMono 2 x-flatMono 2 (1-x))
  else flatMono (k-2+2) x - (k-2:ℕ)*flatMono (k-2+1) x

theorem profile_deriv (k : ℕ) (x : ℝ) :
    HasDerivAt (profile k) (profileDerivative k x) x := by
  unfold profile profileDerivative
  split
  · exact hasDerivAt_id x
  · split
    · exact transitionReciprocal_hasDerivAt x
    · exact flatMono_deriv _ x

def withKind (a : Atom) (k : ℕ) : Atom := (a.1,a.2.1,a.2.2.1,k)
def reflect (a : Atom) : Atom := (a.1,-a.2.1,1-a.2.2.1,a.2.2.2)

end Atom
namespace Circuit
open Nat.Partrec

def atomDiff (j : Fin 4) (a : Atom) : Circuit :=
  if a.1=j then mul (const a.2.1)
    (if a.2.2.2=0 then const 1 else if a.2.2.2=1 then
      mul (const (-1)) (mul (mul (atom a) (atom a))
        (sub (atom (a.withKind 4)) (atom (a.reflect.withKind 4))))
    else sub (atom (a.withKind (a.2.2.2-2+4)))
      (mul (const (a.2.2.2-2:ℕ)) (atom (a.withKind (a.2.2.2-2+3)))))
  else const 0

@[simp] theorem eval_add (a b : Circuit) (z : SpaceTime) :
    eval (add a b) z = eval a z + eval b z := rfl
@[simp] theorem eval_mul (a b : Circuit) (z : SpaceTime) :
    eval (mul a b) z = eval a z * eval b z := rfl

theorem atomDiff_eval (j : Fin 4) (a : Atom) (z : SpaceTime) :
    eval (atomDiff j a) z =
      (a.2.1:ℝ) * Atom.profileDerivative a.2.2.2
        ((a.2.1:ℝ)*coordinateLinear a.1 z+a.2.2.1) * (if a.1=j then 1 else 0) := by
  unfold atomDiff
  split
  · simp only [eval_mul,eval_const,mul_one]
    congr 1
    unfold Atom.profileDerivative
    split
    · simp
    · split
      · rename_i h h0 h1
        have he : (-(a.2.1:ℝ))*coordinateLinear a.1 z+(1-(a.2.2.1:ℝ)) =
            1-((a.2.1:ℝ)*coordinateLinear a.1 z+a.2.2.1) := by ring
        simp only [eval_mul,eval_const,eval_sub,eval_atom]
        simp [Atom.eval,Atom.profile,Atom.withKind,Atom.reflect,h1]
        left
        congr 1
        ring
      · rename_i h h0 h1
        simp only [eval_sub,eval_const,eval_mul,eval_atom]
        simp [Atom.eval,Atom.withKind,Atom.profile,
          show a.2.2.2-2+4≠1 by omega,
          show a.2.2.2-2+3≠1 by omega]
  · simp_all

def diff (j : Fin 4) : Circuit → Circuit
  | .zero | .succ | .left | .right => const 0
  | .pair a b => add (diff j a) (diff j b)
  | .comp a b => add (mul (diff j a) b) (mul a (diff j b))
  | .prec a _ => atomDiff j (data a)
  | .rfind' _ => const 0

theorem diff_correct (e : Circuit) (j : Fin 4) (z : SpaceTime) :
    eval (diff j e) z = fderiv ℝ (eval e) z (spacetimeBasis j) := by
  induction e with
  | zero | succ | left | right => simp [diff,eval]
  | pair a b ha hb =>
      simp only [diff,eval_add,eval,fderiv_fun_add ((smooth a).differentiable (by simp) z)
        ((smooth b).differentiable (by simp) z),add_apply,ha,hb]
  | comp a b ha hb =>
      simp only [diff,eval_add,eval,fderiv_fun_mul ((smooth a).differentiable (by simp) z)
        ((smooth b).differentiable (by simp) z),add_apply,
        smul_apply,smul_eq_mul,ha,hb]
      ring
  | prec a b ha hb =>
      dsimp only [diff,eval]
      rw [atomDiff_eval]
      let v : Atom := data a
      have h := (Atom.profile_deriv v.2.2.2 ((v.2.1:ℝ)*coordinateLinear v.1 z+v.2.2.1)).comp_hasFDerivAt z
        (((coordinateLinear v.1).hasFDerivAt.const_mul (v.2.1:ℝ)).add_const (v.2.2.1:ℝ))
      change _ = fderiv ℝ (Atom.eval v) z (spacetimeBasis j)
      have hh : HasFDerivAt (Atom.eval v)
          (Atom.profileDerivative v.2.2.2 ((v.2.1:ℝ)*coordinateLinear v.1 z+v.2.2.1) •
            (v.2.1:ℝ) • coordinateLinear v.1) z := h
      rw [hh.fderiv]
      simp only [smul_apply,smul_eq_mul,coordinateLinear_basis]
      ring
  | rfind' a ha => simp [diff,eval]

def mixed (e : Circuit) : List (Fin 4) → Circuit
  | [] => e
  | j::α => diff j (mixed e α)

noncomputable def field (e : Fin 3 → Circuit) : Field := fun t x j => eval (e j) (t,x)

theorem field_smooth (e : Fin 3 → Circuit) : Smooth (field e) :=
  contDiff_pi.mpr (fun j => smooth (e j))

theorem mixed_field (e : Fin 3 → Circuit) (α : List (Fin 4)) :
    mixedDerivative (field e) α = fun z j => eval (mixed (e j) α) z := by
  induction α with
  | nil => rfl
  | cons k α ih =>
      ext z j
      rw [mixedDerivative,ih]
      change (fderiv ℝ (fun z j => eval (mixed (e j) α) z) z (spacetimeBasis k)) j = _
      rw [fderiv_pi (fun i => (smooth (mixed (e i) α)).differentiable (by simp) z)]
      exact (diff_correct _ k z).symm

def suml : List Circuit → Circuit
  | [] => const 0
  | e::l => add e (suml l)

@[simp] theorem eval_suml (l : List Circuit) (z : SpaceTime) :
    eval (suml l) z = (l.map (fun e => eval e z)).sum := by
  induction l with
  | nil => simp [suml]
  | cons e l ih => simp [suml,ih]

noncomputable def sum {ι : Type*} [Fintype ι] (f : ι → Circuit) : Circuit :=
  suml (Finset.univ.toList.map f)

@[simp] theorem eval_sum {ι : Type*} [Fintype ι] (f : ι → Circuit) (z : SpaceTime) :
    eval (sum f) z = ∑ i, eval (f i) z := by simp [sum]

noncomputable def polynomial (p : ℚ[X]) (j : Fin 4) (a b : ℚ) : Circuit :=
  suml (p.support.toList.map (fun n => mul (const (p.coeff n)) (atom (j,a,b,n+2))))

theorem eval_polynomial (p : ℚ[X]) (j : Fin 4) (a b : ℚ) (z : SpaceTime) :
    eval (polynomial p j a b) z = flatJet p ((a:ℝ)*coordinateLinear j z+b) := by
  simp only [polynomial,eval_suml,List.map_map,Function.comp_def,eval_mul,eval_const,eval_atom]
  simp only [Atom.eval,Atom.profile, show ∀ n : ℕ, n+2 ≠ 0 by omega,
    show ∀ n : ℕ, n+2 ≠ 1 by omega,ite_false,Nat.add_sub_cancel,flatMono,flatJet]
  simp only [Polynomial.map_pow,Polynomial.map_X,Polynomial.eval_pow,Polynomial.eval_X,
    ← mul_assoc]
  simp only [Finset.sum_map_toList, ← Finset.sum_mul]
  congr 1
  rw [Polynomial.eval_map,Polynomial.eval₂_eq_sum]
  rfl

end Circuit
namespace JetExpr

noncomputable def compile : JetExpr → Fin 4 → ℚ → ℚ → Circuit
  | .const q, _, _, _ => Circuit.const q
  | .id, j, a, b => Circuit.atom (j,a,b,0)
  | .add f g, j, a, b => Circuit.add (f.compile j a b) (g.compile j a b)
  | .mul f g, j, a, b => Circuit.mul (f.compile j a b) (g.compile j a b)
  | .affine c d f, j, a, b => f.compile j (c*a) (c*b+d)
  | .flat p, j, a, b => Circuit.polynomial p j a b
  | .reciprocal, j, a, b => Circuit.atom (j,a,b,1)

theorem compile_correct (e : JetExpr) (j : Fin 4) (a b : ℚ) (z : SpaceTime) :
    Circuit.eval (e.compile j a b) z = e.eval ((a:ℝ)*coordinateLinear j z+b) := by
  induction e generalizing a b with
  | const q => simp [compile,eval]
  | id => simp [compile,eval,Atom.eval,Atom.profile]
  | add e f he hf => simp [compile,eval,he,hf]
  | mul e f he hf => simp [compile,eval,he,hf]
  | affine c d e he =>
      simp only [compile,eval,he,Rat.cast_add,Rat.cast_mul]
      congr 1
      ring
  | flat p => exact Circuit.eval_polynomial _ _ _ _ _
  | reciprocal => simp [compile,eval,Atom.eval,Atom.profile]

end JetExpr
namespace BoxExpr

noncomputable def compile : BoxExpr → Circuit
  | .const q => Circuit.const q
  | .coord j e => e.compile j 1 0
  | .add e f => Circuit.add e.compile f.compile
  | .mul e f => Circuit.mul e.compile f.compile

theorem compile_correct (e : BoxExpr) (z : SpaceTime) :
    Circuit.eval e.compile z = e.eval z := by
  induction e with
  | const q => simp [compile,eval]
  | coord j e => simpa [compile,eval] using e.compile_correct j 1 0 z
  | add e f he hf => simp [compile,eval,he,hf]
  | mul e f he hf => simp [compile,eval,he,hf]

end BoxExpr
end Solenoidal

end OAI
