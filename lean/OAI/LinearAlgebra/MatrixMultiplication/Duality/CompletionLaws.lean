import OAI.LinearAlgebra.MatrixMultiplication.Completion.ColorLaws
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.BaseTensorBudgets
import OAI.LinearAlgebra.MatrixMultiplication.Duality.WitnessArithmetic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualCompletionLaws

attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels CompletionColorLaws

universe u
variable {X Y Z : Type u} [Fintype X] [Fintype Y] [Fintype Z]

abbrev Laws (S : FlaggedTensor X Y Z) := ∀ c, FiniteLaw (ColorSlice S c)

def gibbsWeight (a b : ℝ) : ℝ := Real.exp a / (Real.exp a + Real.exp b)

theorem gibbsWeight_nonneg (a b : ℝ) : 0 ≤ gibbsWeight a b :=
  div_nonneg (Real.exp_pos a).le (add_pos (Real.exp_pos a) (Real.exp_pos b)).le

theorem gibbsWeight_lt_one (a b : ℝ) : gibbsWeight a b < 1 := by
  apply (div_lt_one (add_pos (Real.exp_pos a) (Real.exp_pos b))).mpr
  linarith [Real.exp_pos b]

def minusLaws (S : FlaggedTensor X Y Z) (p : Laws S) (m : ℕ) (hm : 0 < m)
    (rho : ℝ) (hrho0 : 0 < rho) (hrho1 : rho < 1) : Laws (complete S .B m)
  | .B => conditionalCompletionLaw S .B .B (p .B) (p .B) m hm 0 (by norm_num) (by norm_num)
  | .A => conditionalCompletionLaw S .B .A (p .B) (p .A) m hm rho hrho0.le hrho1
  | .C => conditionalCompletionLaw S .B .C (p .B) (p .C) m hm rho hrho0.le hrho1

def plusALaws (S : FlaggedTensor X Y Z) (p : Laws S) (m : ℕ) (hm : 0 < m)
    (rho hA hC : ℝ) (hrho0 : 0 < rho) (hrho1 : rho < 1) : Laws (complete S .A m)
  | .B => conditionalCompletionLaw S .A .B (p .A) (p .B) m hm (1 - rho)
      (sub_nonneg.mpr hrho1.le) (by linarith)
  | .A => conditionalCompletionLaw S .A .A (p .A) (p .A) m hm 0 (by norm_num) (by norm_num)
  | .C => conditionalCompletionLaw S .A .C (p .A) (p .C) m hm (gibbsWeight hA hC)
      (gibbsWeight_nonneg hA hC) (gibbsWeight_lt_one hA hC)

def plusCLaws (S : FlaggedTensor X Y Z) (p : Laws S) (m : ℕ) (hm : 0 < m)
    (rho hA hC : ℝ) (hrho0 : 0 < rho) (hrho1 : rho < 1) : Laws (complete S .C m)
  | .B => conditionalCompletionLaw S .C .B (p .C) (p .B) m hm (1 - rho)
      (sub_nonneg.mpr hrho1.le) (by linarith)
  | .A => conditionalCompletionLaw S .C .A (p .C) (p .A) m hm (gibbsWeight hC hA)
      (gibbsWeight_nonneg hC hA) (gibbsWeight_lt_one hC hA)
  | .C => conditionalCompletionLaw S .C .C (p .C) (p .C) m hm 0 (by norm_num) (by norm_num)

def baseLeaf : (c : Color) → ColorSlice BaseTwo.flagged c
  | .B => ⟨⟨(1, 0, 0), by norm_num [BaseTwo.flagged, BaseTwo.tensor]⟩,
      by simp [leafColor, BaseTwo.flagged, BaseTwo.flagB]⟩
  | .A => ⟨⟨(0, 0, 1), by norm_num [BaseTwo.flagged, BaseTwo.tensor]⟩,
      by simp [leafColor, BaseTwo.flagged, BaseTwo.flagB, BaseTwo.flagA]⟩
  | .C => ⟨⟨(0, 1, 0), by norm_num [BaseTwo.flagged, BaseTwo.tensor]⟩,
      by simp [leafColor, BaseTwo.flagged, BaseTwo.flagB, BaseTwo.flagA]⟩

def baseLaws : Laws BaseTwo.flagged := fun c => FiniteLaw.pure (baseLeaf c)

def script2 : Script := .step .base .B 2
def script4 : Script := .step script2 .A 2
def script8 : Script := .step script4 .C 2
def script24 : Script := .step script8 .B 3
def script48 : Script := .step script24 .C 2
def script96 : Script := .step script48 .B 2

def laws2 : Laws (Script.tensor BaseTwo.flagged script2) :=
  minusLaws BaseTwo.flagged baseLaws 2 (Nat.zero_lt_succ 1) (1 / 2) (by norm_num) (by norm_num)

def laws4 : Laws (Script.tensor BaseTwo.flagged script4) :=
  plusALaws (Script.tensor BaseTwo.flagged script2) laws2 2 (Nat.zero_lt_succ 1)
    DualWitness.state2.rho DualWitness.state2.hA DualWitness.state2.hC
    (by norm_num [DualWitness.state2, DualWitness.initial, DualWitness.minus])
    (by norm_num [DualWitness.state2, DualWitness.initial, DualWitness.minus])

def laws8 : Laws (Script.tensor BaseTwo.flagged script8) :=
  plusCLaws (Script.tensor BaseTwo.flagged script4) laws4 2 (Nat.zero_lt_succ 1)
    DualWitness.state4.rho DualWitness.state4.hA DualWitness.state4.hC
    (by norm_num [DualWitness.state4, DualWitness.state2, DualWitness.initial,
      DualWitness.minus, DualWitness.plusA])
    (by norm_num [DualWitness.state4, DualWitness.state2, DualWitness.initial,
      DualWitness.minus, DualWitness.plusA])

def laws24 : Laws (Script.tensor BaseTwo.flagged script24) :=
  minusLaws (Script.tensor BaseTwo.flagged script8) laws8 3 (Nat.zero_lt_succ 2)
    DualWitness.state8.rho
    (by rw [DualWitness.state8_rho]; exact DualWitness.rho8_range.1)
    (by rw [DualWitness.state8_rho]; exact DualWitness.rho8_range.2)

def laws48 : Laws (Script.tensor BaseTwo.flagged script48) :=
  plusCLaws (Script.tensor BaseTwo.flagged script24) laws24 2 (Nat.zero_lt_succ 1)
    DualWitness.state24.rho DualWitness.state24.hA DualWitness.state24.hC
    (by rw [DualWitness.state24_rho]; exact DualWitness.rho24_range.1)
    (by rw [DualWitness.state24_rho]; exact DualWitness.rho24_range.2)

def laws96 : Laws (Script.tensor BaseTwo.flagged script96) :=
  minusLaws (Script.tensor BaseTwo.flagged script48) laws48 2 (Nat.zero_lt_succ 1)
    DualWitness.state48.rho
    (by rw [DualWitness.state48_rho]; exact DualWitness.rho48_range.1)
    (by rw [DualWitness.state48_rho]; exact DualWitness.rho48_range.2)

def laws288 : Laws (Script.tensor BaseTwo.flagged Script.dual) :=
  plusALaws (Script.tensor BaseTwo.flagged script96) laws96 3 (Nat.zero_lt_succ 2)
    DualWitness.state96.rho DualWitness.state96.hA DualWitness.state96.hC
    (by rw [DualWitness.state96_rho]; exact DualWitness.rho96_range.1)
    (by rw [DualWitness.state96_rho]; exact DualWitness.rho96_range.2)

end MatrixMultiplication.DualCompletionLaws

end

end OAI
