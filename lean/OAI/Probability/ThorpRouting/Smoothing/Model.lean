import Mathlib

namespace OAI

namespace ThorpNine.Smoothing

namespace Thorp
open scoped BigOperators
open Filter

abbrev Card (d : ℕ) := Fin d → Bool

def switchFun {d : ℕ} (ξ : Card d → Bool) (x : Card (d + 1)) : Card (d + 1) :=
  Fin.cons (Bool.xor (x 0) (ξ (Fin.tail x))) (Fin.tail x)

theorem switchFun_involutive {d : ℕ} (ξ : Card d → Bool) :
    Function.Involutive (switchFun ξ) := by
  intro x
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [switchFun, Fin.cons_zero, Fin.tail_cons]
    cases x 0 <;> cases ξ (Fin.tail x) <;> rfl
  · simp [switchFun, Fin.tail]

def pairSwitch {d : ℕ} (ξ : Card d → Bool) : Equiv.Perm (Card (d + 1)) :=
  { toFun := switchFun ξ
    invFun := switchFun ξ
    left_inv := switchFun_involutive ξ
    right_inv := switchFun_involutive ξ }

def Butterfly : ℕ → Type
  | 0 => Unit
  | d + 1 => (Card d → Bool) × (Bool → Butterfly d)

def childLift {d : ℕ} (p : Bool → Equiv.Perm (Card d)) : Equiv.Perm (Card (d + 1)) where
  toFun x := Fin.cons (x 0) (p (x 0) (Fin.tail x))
  invFun x := Fin.cons (x 0) ((p (x 0)).symm (Fin.tail x))
  left_inv x := by simp only [Fin.cons_zero, Fin.tail_cons, Equiv.symm_apply_apply, Fin.cons_self_tail]
  right_inv x := by simp only [Fin.cons_zero, Fin.tail_cons, Equiv.apply_symm_apply, Fin.cons_self_tail]

def butterflyPerm : (d : ℕ) → Butterfly d → Equiv.Perm (Card d)
  | 0, _ => 1
  | d + 1, b => pairSwitch b.1 * childLift (fun ε => butterflyPerm d (b.2 ε))

noncomputable def finiteMean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

def SwitchIndex : ℕ → Type
  | 0 => Empty
  | d + 1 => Sum (Card d) (Bool × SwitchIndex d)

instance (d : ℕ) : Fintype (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype Empty)
  | succ d ih => exact inferInstanceAs (Fintype (Sum (Card d) (Bool × SwitchIndex d)))

instance (d : ℕ) : DecidableEq (SwitchIndex d) := by
  induction d with
  | zero => exact inferInstanceAs (DecidableEq Empty)
  | succ d ih => exact inferInstanceAs (DecidableEq (Sum (Card d) (Bool × SwitchIndex d)))

def decodeButterfly : (d : ℕ) → (SwitchIndex d → Bool) → Butterfly d
  | 0, _ => ()
  | d + 1, ω => (fun y => ω (Sum.inl y), fun ε =>
      decodeButterfly d (fun i => ω (Sum.inr (ε,i))))

end Thorp

namespace Thorp.PairRouting
open scoped BigOperators
open Filter
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

noncomputable def tupleProbability {Ω β : Type*} [Fintype Ω] [DecidableEq β]
    (P : Ω → Equiv.Perm β) (x y : ι → β) : ℝ := by
  classical
  exact finiteMean (fun ω => if ∀ i, P ω (x i) = y i then 1 else 0)

end Thorp.PairRouting

namespace Thorp.StrongSmoothing

def coordinateRelabel (d : ℕ) (order : Equiv.Perm (Fin d)) : Equiv.Perm (Card d) where
  toFun x := fun i => x (order.symm i)
  invFun x := fun i => x (order i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

def sweep (d : ℕ) (order : Equiv.Perm (Fin d)) (ω : SwitchIndex d → Bool) :
    Equiv.Perm (Card d) :=
  coordinateRelabel d order * butterflyPerm d (decodeButterfly d ω) *
    (coordinateRelabel d order)⁻¹

abbrev Tuples (d l : ℕ) := Fin l ↪ Card d

noncomputable def sweepKernel (d l : ℕ) (order : Equiv.Perm (Fin d)) :
    Matrix (Tuples d l) (Tuples d l) ℝ :=
  fun x y => PairRouting.tupleProbability (sweep d order) x y

noncomputable def reflectedKernel (d l : ℕ) (order : Equiv.Perm (Fin d)) (orientation : Bool) :
    Matrix (Tuples d l) (Tuples d l) ℝ :=
  let A := sweepKernel d l order
  if orientation then A * A.transpose else A.transpose * A

noncomputable def regularAbsoluteEvenTrace (d : ℕ) (order : Equiv.Perm (Fin d)) (u : ℕ) : ℝ :=
  Matrix.trace ((reflectedKernel d (2^d) order false)^u)

def MainStatement : Prop :=
  ∃ u : ℕ, 1 ≤ u ∧ ∃ C : ℝ,
    (∀ d l : ℕ, l ≤ 2^d → ∀ order : Equiv.Perm (Fin d), ∀ orientation : Bool,
      ∀ x y : Tuples d l,
        ((reflectedKernel d l order orientation)^u) x y ≤
          Real.exp (C*l)/((2^d).descFactorial l:ℝ)) ∧
    (∀ d : ℕ, ∀ order : Equiv.Perm (Fin d),
      regularAbsoluteEvenTrace d order u ≤ Real.exp (C*(2:ℝ)^d))

end Thorp.StrongSmoothing

end ThorpNine.Smoothing

end OAI
