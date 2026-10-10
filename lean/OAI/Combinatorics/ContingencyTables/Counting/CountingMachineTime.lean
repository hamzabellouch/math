import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordRationalLaw
import OAI.Combinatorics.ContingencyTables.Counting.CountingPublicInputBounds
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileRuntimeBound

namespace OAI

/-! # Uniform public time from the counting word budget -/
namespace ContingencyTables.CountingMachineTime
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.LiteralCodec
open CountingPublicInputBounds Polynomial
open scoped Classical
noncomputable section

variable {wordCount : List Symbol→ℕ} {output : List Symbol×List Bool→List Symbol}

theorem public_bound (N : Realizer wordCount) (F : Realizer output)
    (hN : PolynomialTime N) (hF : PolynomialTime F) (p : Polynomial ℕ)
    (hb : ∀ (m n : ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
      (epsilon delta : ℚ), 0 < epsilon → 0 < delta →
      wordCount (Algorithms.encodeCountingInput r c b epsilon delta) ≤
        p.eval (size r c b epsilon delta)) :
    ∃ C d : ℕ, 0 < C ∧
      ∀ (m n : ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
        (epsilon delta : ℚ), 0 < epsilon → 0 < delta →
        FiniteWordExecution.machineTime N F (Algorithms.encodeCountingInput r c b epsilon delta) ≤
          Algorithms.countingTime C d r c b epsilon delta := by
  obtain ⟨q,hq⟩ := FiniteWordExecution.machineTime_polynomial hN hF
  let P : Polynomial ℕ := q.comp (18*X+1+p)
  refine ⟨P.eval 1+1,P.natDegree,by omega,?_⟩
  intro m n r c b epsilon delta he hd
  let S := size r c b epsilon delta
  have hS : 1 ≤ S := by unfold S size; omega
  have hlen : (Algorithms.encodeCountingInput r c b epsilon delta).length ≤ S := by
    unfold S size
    omega
  have hm : FiniteWordExecution.wordMeasure wordCount
      (Algorithms.encodeCountingInput r c b epsilon delta) ≤ (18*X+1+p).eval S := by
    unfold FiniteWordExecution.wordMeasure
    rw [weight_word]
    simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
    exact Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 18 hlen) 1)
      (hb m n r c b epsilon delta he hd)
  calc
    _ ≤ q.eval (FiniteWordExecution.wordMeasure wordCount
        (Algorithms.encodeCountingInput r c b epsilon delta)) := hq _
    _ ≤ q.eval ((18*X+1+p).eval S) := polynomial_eval_monotone q hm
    _ = P.eval S := by simp only [P,Polynomial.eval_comp]
    _ ≤ P.eval 1*S^P.natDegree := by
      simpa only [one_mul,pow_one] using ProfilePrograms.polynomial_scaled_power P 1 S 1 hS
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_succ _)

end
end ContingencyTables.CountingMachineTime

end OAI
