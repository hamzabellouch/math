import Mathlib
import OAI.Computability.MaxCut.PCP.GraphTableComplexity

namespace OAI

/-! Polynomial arithmetic for the actual initial-machine phase counts. The
separate execution theorem must connect these counts to the concrete program. -/

namespace MaxCutGames.Foundations.PCP.RawInitialMachineBudget

open Target Complexity

def nameSum {n : Nat} (c : Clause n) : Nat :=
  (c)[0].variableIndex.val + (c)[1].variableIndex.val + (c)[2].variableIndex.val

def bodyTime {n : Nat} (i : Nat) (c : Clause n) : Nat :=
  6 * n + 18 * i + 2 * nameSum c +
    2 * (encodeWords (Complexity.clauseWords c)).length + 63

def loopTime {n : Nat} (i : Nat) : List (Clause n) → Nat
  | [] => 1
  | c :: cs => bodyTime i c + loopTime (i + 1) cs

theorem nameSum_le {n : Nat} (c : Clause n) : nameSum c ≤ 3 * n := by
  have h0 := (c)[0].variableIndex.isLt
  have h1 := (c)[1].variableIndex.isLt
  have h2 := (c)[2].variableIndex.isLt
  unfold nameSum
  omega

theorem bodyTime_le {n : Nat} (i : Nat) (c : Clause n) :
    bodyTime i c ≤ 18 * n + 18 * i + 81 := by
  have hn := nameSum_le c
  have hb := clauseBits_length_le c
  unfold bodyTime
  omega

theorem loopTime_le {n : Nat} (i : Nat) (cs : List (Clause n)) :
    loopTime i cs ≤ cs.length * (18 * n + 18 * (i + cs.length) + 81) + 1 := by
  induction cs generalizing i with
  | nil => simp [loopTime]
  | cons c cs ih =>
      have hc := bodyTime_le i c
      have ht := ih (i + 1)
      have hbound : bodyTime i c ≤ 18 * n + 18 * (i + (c :: cs).length) + 81 := by
        simp only [List.length_cons]
        omega
      have hsame : 18 * n + 18 * (i + 1 + cs.length) + 81 =
          18 * n + 18 * (i + (c :: cs).length) + 81 := by
        simp only [List.length_cons]
        omega
      rw [hsame] at ht
      rw [loopTime]
      calc
        _ ≤ (18 * n + 18 * (i + (c :: cs).length) + 81) +
            (cs.length * (18 * n + 18 * (i + (c :: cs).length) + 81) + 1) :=
          Nat.add_le_add hbound ht
        _ = _ := by rw [List.length_cons]; ring

theorem input_header_bound (F : Formula) :
    F.«variables» + F.clauses.length + 2 ≤ (formulaBits F).length := by
  simp only [formulaBits, formulaWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

theorem graph_size_bound (F : Formula) :
    (RawInitialTables.table F).vertices + (RawInitialTables.table F).darts ≤
      7 * (formulaBits F).length := by
  rw [RawInitialTables.initial_size]
  have h := input_header_bound F
  omega

def fullBudget (F : Formula) : Nat :=
  6 * F.«variables» + 10 * F.clauses.length + 30 + loopTime 0 F.clauses +
    (GraphTables.tableBits (RawInitialTables.table F)).length

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 100 * Polynomial.X ^ 2 + Polynomial.C 60000 * Polynomial.X +
    Polynomial.C 100

theorem timePolynomial_eval (N : Nat) :
    timePolynomial.eval N = 100 * N ^ 2 + 60000 * N + 100 := by
  simp [timePolynomial]

theorem fullBudget_le (F : Formula) :
    fullBudget F ≤ timePolynomial.eval (formulaBits F).length := by
  have hinput := input_header_bound F
  have hloop := loopTime_le 0 F.clauses
  have hout := GraphTableComplexity.bits_le_of_size_le (RawInitialTables.table F)
    (graph_size_bound F)
  rw [GraphTableComplexity.encodingPolynomial_eval] at hout
  simp only [Nat.zero_add] at hloop
  have hm : F.clauses.length ≤ (formulaBits F).length := by omega
  have hcoefficient : 18 * F.«variables» + 18 * F.clauses.length + 81 ≤
      18 * (formulaBits F).length + 81 := by omega
  have hproduct := Nat.mul_le_mul hm hcoefficient
  rw [timePolynomial_eval]
  unfold fullBudget
  nlinarith

end MaxCutGames.Foundations.PCP.RawInitialMachineBudget

end OAI
