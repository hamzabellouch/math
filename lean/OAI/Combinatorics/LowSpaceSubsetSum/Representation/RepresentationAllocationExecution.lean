import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CountedBinomial
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredLog2
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationAllocation

namespace OAI

/-! # Executing the six binomial widths and eight background sizes

The binomial loop uses integer multiplication and exact division with constant
state. Its bounded binary-log loop is followed by the fixed two-level integer
allocation formulas. No real logarithm is evaluated by this routine.
-/

namespace LowSpaceSubsetSum.RepresentationAllocationExecution

open scoped BigOperators

def bits (m k : ℕ) : ℕ × ℕ :=
  let choose := CountedBinomial.run m k
  let log := MeasuredLog2.run m choose.value
  (log.1, 8 * choose.steps + log.2 + 8)

theorem bits_value (m k : ℕ) : (bits m k).1 = binomialBits m k := by
  simp only [bits, CountedBinomial.run_value, MeasuredLog2.run_value m _ (Nat.choose_le_two_pow m k),
    binomialBits]

theorem bits_work (m k : ℕ) : (bits m k).2 ≤ 11 * m + 9 := by
  have hc := CountedBinomial.run_steps m k
  have hl := MeasuredLog2.run_work m (CountedBinomial.run m k).value
  change 8 * (CountedBinomial.run m k).steps +
    (MeasuredLog2.run m (CountedBinomial.run m k).value).2 + 8 ≤ _
  omega

def run (n : ℕ) (guesses : Vector ℕ 3) : Vector ℕ 8 × ℕ :=
  let bs := Vector.ofFn (fun side : Fin 2 => Vector.ofFn (fun j : Fin 3 =>
    bits (mixerSize n) (if side = 0 then guesses[j.val] else mixerSize n / 2 - guesses[j.val])))
  let counts := computedLeafCounts (representationBackgroundSize n)
    bs[0][0].1 bs[1][0].1 bs[0][1].1 bs[1][1].1 bs[0][2].1 bs[1][2].1
  (Vector.ofFn counts, (∑ side : Fin 2, ∑ j : Fin 3, bs[side.val][j.val].2) + 100)

theorem value (n : ℕ) (guesses : Vector ℕ 3) (g : RepresentationSetup.Guesses n)
    (hg : ∀ j : Fin 3, guesses[j.val] = (g j).val) (i : Fin 8) :
    (run n guesses).1[i.val] = representationLeafCounts n g i := by
  simp [run, bits_value, hg, representationLeafCounts, representationBits, representationCount]

theorem work (n : ℕ) (guesses : Vector ℕ 3) :
    (run n guesses).2 ≤ 100 * (n + 2) := by
  have hs := Finset.sum_le_sum (fun side (_ : side ∈ (Finset.univ : Finset (Fin 2))) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
      bits_work (mixerSize n) (if side = 0 then guesses[j.val] else mixerSize n / 2 - guesses[j.val])))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
  have hm : mixerSize n ≤ n := by unfold mixerSize; omega
  change (∑ side : Fin 2, ∑ j : Fin 3,
    (bits (mixerSize n) (if side = 0 then guesses[j.val] else mixerSize n / 2 - guesses[j.val])).2) + 100 ≤ _
  omega

end LowSpaceSubsetSum.RepresentationAllocationExecution

end OAI
