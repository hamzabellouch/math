import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.NormNum

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualWitness

structure State where
  rho : ℝ
  factors : ℕ
  hB : ℝ
  hA : ℝ
  hC : ℝ

def initial : State := ⟨1 / 2, 1, 0, 0, 0⟩

def minus (m : ℕ) (s : State) : State :=
  let rho' := s.rho ^ m
  { rho := rho'
    factors := m * s.factors
    hB := m * s.hB
    hA := m * ((s.rho - rho') / (1 - rho') * s.hB +
      (1 - s.rho) / (1 - rho') * s.hA)
    hC := m * ((s.rho - rho') / (1 - rho') * s.hB +
      (1 - s.rho) / (1 - rho') * s.hC) }

def plusA (m : ℕ) (s : State) : State :=
  let rho' := 1 - (1 - s.rho) ^ m
  { rho := rho'
    factors := m * s.factors
    hB := m * (s.rho / rho' * s.hB + (rho' - s.rho) / rho' * s.hA)
    hA := m * s.hA
    hC := Real.log ((Real.exp s.hA + Real.exp s.hC) ^ m - Real.exp (m * s.hA)) }

def plusC (m : ℕ) (s : State) : State :=
  let rho' := 1 - (1 - s.rho) ^ m
  { rho := rho'
    factors := m * s.factors
    hB := m * (s.rho / rho' * s.hB + (rho' - s.rho) / rho' * s.hC)
    hA := Real.log ((Real.exp s.hC + Real.exp s.hA) ^ m - Real.exp (m * s.hC))
    hC := m * s.hC }

def state2 : State := minus 2 initial
def state4 : State := plusA 2 state2
def state8 : State := plusC 2 state4
def state24 : State := minus 3 state8
def state48 : State := plusC 2 state24
def state96 : State := minus 2 state48
def state288 : State := plusA 3 state96

def normalizedHidden (s : State) : ℝ :=
  (s.rho * s.hB + (1 - s.rho) * max s.hA s.hC) / s.factors

def rho8 : ℝ := 1 - (3 / 4 : ℝ) ^ 4
def rho24 : ℝ := rho8 ^ 3
def delta24 : ℝ := 3 * (1 - rho8) / (1 - rho24) * Real.log (9 / 7 : ℝ)
def z48 : ℝ := Real.log ((1 + Real.exp (-delta24)) ^ 2 - 1)
def rho48 : ℝ := 1 - (1 - rho24) ^ 2
def rho96 : ℝ := rho48 ^ 2
def delta96 : ℝ := 2 * z48 / (1 + rho48)
def rho288 : ℝ := 1 - (1 - rho96) ^ 3
def z288 : ℝ := Real.log ((1 + Real.exp (-delta96)) ^ 3 - 1)
def hiddenRate : ℝ := 9 / 64 * Real.log 3 +
  (1 - rho48) / 48 * z48 + (1 - rho288) / 288 * z288
def aspect : ℝ := 2 * hiddenRate / Real.log 2

theorem state_factors : state288.factors = 288 := by
  norm_num [state288, state96, state48, state24, state8, state4, state2,
    initial, minus, plusA, plusC]

theorem state8_rho : state8.rho = rho8 := by
  norm_num [state8, state4, state2, initial, minus, plusA, plusC, rho8]

theorem state24_rho : state24.rho = rho24 := by
  simp only [state24, minus, rho24, state8_rho]

theorem state48_rho : state48.rho = rho48 := by
  simp only [state48, plusC, rho48, state24_rho]

theorem state96_rho : state96.rho = rho96 := by
  simp only [state96, minus, rho96, state48_rho]

theorem state288_rho : state288.rho = rho288 := by
  simp only [state288, plusA, rho288, state96_rho]

theorem rho8_range : 0 < rho8 ∧ rho8 < 1 := by norm_num [rho8]
theorem rho24_range : 0 < rho24 ∧ rho24 < 1 := by norm_num [rho24, rho8]
theorem rho48_range : 0 < rho48 ∧ rho48 < 1 := by norm_num [rho48, rho24, rho8]
theorem rho96_range : 0 < rho96 ∧ rho96 < 1 := by norm_num [rho96, rho48, rho24, rho8]
theorem rho288_range : 0 < rho288 ∧ rho288 < 1 := by
  norm_num [rho288, rho96, rho48, rho24, rho8]

end MatrixMultiplication.DualWitness

end

end OAI
