import OAI.Combinatorics.ContingencyTables.Machines.FractionOutputProgram
import OAI.Combinatorics.ContingencyTables.Sampling.GreedyPublicMachine
import OAI.Combinatorics.ContingencyTables.Machines.MatrixEncoding

namespace OAI

/-! # The public counting input contains no tape blanks -/

namespace ContingencyTables.CountingInputSymbols
open MatchingFPRAS Algorithms

lemma nat_nonzero (n : ℕ) (a : MatchingFPRAS.Symbol) (ha : a∈encodeNat n) : a≠0 :=
  (FractionOutputProgram.natWord_symbols n a ha).1

lemma int_nonzero (n : ℤ) (a : MatchingFPRAS.Symbol) (ha : a∈encodeInt n) : a≠0 := by
  simp only [encodeInt,List.mem_append] at ha
  rcases ha with ha | ha
  · split_ifs at ha <;> simp only [List.mem_singleton] at ha <;> subst a <;> decide
  · exact nat_nonzero _ a ha

lemma rat_nonzero (q : ℚ) (a : MatchingFPRAS.Symbol) (ha : a∈encodeRat q) : a≠0 := by
  simp only [encodeRat,List.mem_append] at ha
  rcases ha with ha | ha
  · exact int_nonzero _ a ha
  · exact nat_nonzero _ a ha

lemma matrix_nonzero {m n : ℕ} (X : Fin m→Fin n→ℕ)
    (a : MatchingFPRAS.Symbol) (ha : a∈encodeMatrix X) : a≠0 := by
  rw [encodeMatrix_flat] at ha
  obtain ⟨k,_,hk⟩ := List.mem_flatMap.mp ha
  exact nat_nonzero k a hk

lemma counting_nonzero {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ)
    (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ) :
    ∀ a∈encodeCountingInput r c b epsilon delta,a≠0 := by
  intro a ha
  simp only [encodeCountingInput,List.mem_append] at ha
  rcases ha with ((ha | ha) | ha) | ha
  · exact GreedyFeasibleTable.encodeMargins_nonzero r c a ha
  · exact matrix_nonzero b a ha
  · exact rat_nonzero epsilon a ha
  · exact rat_nonzero delta a ha

end ContingencyTables.CountingInputSymbols

end OAI
