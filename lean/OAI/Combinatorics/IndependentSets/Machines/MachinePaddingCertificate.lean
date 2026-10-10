import Mathlib
import OAI.Combinatorics.IndependentSets.Expansion.PreprocessingPaddingWords
import OAI.Combinatorics.IndependentSets.Machines.MachinePaddingBounds

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachinePaddingCertificate

open MachinePaddingRows

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  MachinePaddingBounds.timePolynomial d + 1

def execution (d : Nat) (hd : 0 < d) (count v e : Nat) (output : List Bool) :
    StateTransition.EvalsToInTime (machine d hd).step
      ⟨some (.inr .initialize), (((), none), ()), initialTapes v e count output⟩
      (some (cfg d none (v + count) (e + count * d) 0
        (output ++ paddingBits d v e count)))
      ((timePolynomial d).eval (MachinePaddingBounds.inputSize v e count output)) where
  steps := steps d v e output count + 1
  evals_in_steps := by
    convert paddingTrace d hd count v e output using 1
    rfl
  steps_le_m := by
    simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_one]
    exact Nat.add_le_add_right
      (MachinePaddingBounds.timePolynomial_bounds d v e count output) 1

end IndependentSetsGames.Foundations.Complexity.MachinePaddingCertificate
namespace IndependentSetsGames.Foundations.Complexity.MachinePaddingTable

open PCP MachinePaddingRows

def initialOutput {n d m : Nat} (table : PortTables.Table n d) : List Bool :=
  encodeWords [m, m * d] ++ PreprocessingPaddingWords.rowsBits table

def execution {n d m : Nat} (table : PortTables.Table n d) (h : n ≤ m) (hd : 0 < d) :
    StateTransition.EvalsToInTime (machine d hd).step
      ⟨some (.inr .initialize), (((), none), ()),
        initialTapes n (n * d) (m - n) (initialOutput (m := m) table)⟩
      (some (cfg d none m (m * d) 0
        (PortTables.tableBits (PreprocessingPaddingTables.pad table h))))
      ((MachinePaddingCertificate.timePolynomial d).eval
        (MachinePaddingBounds.inputSize n (n * d) (m - n) (initialOutput (m := m) table))) where
  steps := steps d n (n * d) (initialOutput (m := m) table) (m - n) + 1
  evals_in_steps := by
    have run := paddingTrace d hd (m - n) n (n * d) (initialOutput (m := m) table)
    have hv : n + (m - n) = m := Nat.add_sub_of_le h
    have he : n * d + (m - n) * d = m * d := by rw [← Nat.add_mul, hv]
    have hout : initialOutput (m := m) table ++ paddingBits d n (n * d) (m - n) =
        PortTables.tableBits (PreprocessingPaddingTables.pad table h) := by
      rw [PreprocessingPaddingWords.tableBits_pad]
      rfl
    rw [hv, he, hout] at run
    convert run using 1
    rfl
  steps_le_m := by
    simp only [MachinePaddingCertificate.timePolynomial, Polynomial.eval_add, Polynomial.eval_one]
    exact Nat.add_le_add_right
      (MachinePaddingBounds.timePolynomial_bounds d n (n * d) (m - n) (initialOutput (m := m) table)) 1

end IndependentSetsGames.Foundations.Complexity.MachinePaddingTable

end OAI
