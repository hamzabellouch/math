import OAI.Analysis.Cotype.WalshSymmetry
import OAI.Analysis.Cotype.FrameOrbit
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases

namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
abbrev BinarySpace (n : ℕ) := Fin n → ZMod 2

def binaryBit (b : Bool) : ZMod 2 := if b then 1 else 0

theorem binary_eq_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  have hlt := z.val_lt
  have hval : z.val = 0 ∨ z.val = 1 := by omega
  exact hval.imp (ZMod.val_eq_zero z).mp (ZMod.val_eq_one (by decide) z).mp

def bitEquiv : Bool ≃ ZMod 2 where
  toFun := binaryBit
  invFun z := decide (z = 1)
  left_inv b := by cases b <;> simp [binaryBit]
  right_inv z := by rcases binary_eq_zero_or_one z with rfl | rfl <;> decide

def cubeBinaryEquiv (n : ℕ) : Cube n ≃ BinarySpace n :=
  Equiv.piCongrRight (fun _ => bitEquiv)

@[simp] theorem cubeBinaryEquiv_apply {n : ℕ} (u : Cube n) (i : Fin n) :
    cubeBinaryEquiv n u i = binaryBit (u i) := rfl

def binarySign (z : ZMod 2) : ℝ := if z = 0 then 1 else -1

@[simp] theorem binarySign_zero : binarySign 0 = 1 := by simp [binarySign]
@[simp] theorem binarySign_one : binarySign 1 = -1 := by simp [binarySign]

theorem binarySign_add (a b : ZMod 2) :
    binarySign (a+b) = binarySign a * binarySign b := by
  have ha := binary_eq_zero_or_one a
  have hb := binary_eq_zero_or_one b
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp [show (1 + 1 : ZMod 2) = 0 by decide]

theorem binarySign_injective : Function.Injective binarySign := by
  intro a b h
  rcases binary_eq_zero_or_one a with rfl | rfl <;>
    rcases binary_eq_zero_or_one b with rfl | rfl <;> norm_num [binarySign] at *

theorem binarySign_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    binarySign (∑ i ∈ s, f i) = ∏ i ∈ s, binarySign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, binarySign_add, ih]

theorem character_binary_dot {n : ℕ} (u v : Cube n) :
    character v u = binarySign (coordinateDual (cubeBinaryEquiv n v) (cubeBinaryEquiv n u)) := by
  rw [coordinateDual_apply, binarySign_sum]
  apply Finset.prod_congr rfl
  intro i hi
  cases hu : u i <;> cases hv : v i <;> simp [binaryBit, sign, hu, hv]

def BinaryFrame {n r : ℕ} (U : Fin r → Cube n) : Prop :=
  LinearIndependent (ZMod 2) (fun i => cubeBinaryEquiv n (U i))

end Cotype

end

end OAI
