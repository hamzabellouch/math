import OAI.Combinatorics.LowSpaceSubsetSum.Storage.CanonicalGuesses

namespace OAI

/-! # Three bounded interval draws stored as a small integer array -/

noncomputable section
namespace LowSpaceSubsetSum.GuessArrayExecution

open scoped BigOperators

def coupling (n : ℕ) : SamplerCoupling (RepresentationSetup.Guesses n) :=
  SamplerCoupling.pi 3 (fun _ => ↥(RepresentationSetup.guessRange n))
    (fun _ => CanonicalGuesses.coupling n)

def execution (n : ℕ) : SamplerExecution.Execution (coupling n) :=
  SamplerExecution.pi 3 _ _ (fun _ => CanonicalGuesses.execution n)

theorem execution_bounded (n : ℕ) : (execution n).Bounded (3 * n ^ 3) 0 := by
  have h := SamplerExecution.pi_bounded 3 (fun _ => ↥(RepresentationSetup.guessRange n))
    (fun _ => CanonicalGuesses.coupling n) (fun _ => CanonicalGuesses.execution n)
    (fun _ => n ^ 3) (fun _ => 0) (fun _ => CanonicalGuesses.execution_bounded n)
  simpa only [execution, coupling, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_zero] using h

def run (n : ℕ) (s : (coupling n).Seed) : Option (Vector ℕ 3) × ℕ :=
  let out := (execution n).run s
  (out.value.map (fun g => Vector.ofFn (fun i => (g i).val)), out.reads + out.tests + 7)

theorem value (n : ℕ) (s : (coupling n).Seed) :
    (run n s).1 = ((coupling n).bounded s).map (fun g => Vector.ofFn (fun i => (g i).val)) := by
  simp only [run, (execution n).value_eq]

theorem work (n : ℕ) (s : (coupling n).Seed) : (run n s).2 ≤ 3 * n ^ 3 + 7 := by
  have h := execution_bounded n s
  change (run n s).2 ≤ _
  change ((execution n).run s).reads + ((execution n).run s).tests + 7 ≤ _
  omega

end LowSpaceSubsetSum.GuessArrayExecution

end

end OAI
