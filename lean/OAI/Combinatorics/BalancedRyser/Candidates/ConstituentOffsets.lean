import Mathlib.Probability.Distributions.Uniform

namespace OAI

namespace Balanced
open scoped _root_.Balanced

abbrev ConstituentOffsets (D K : Type*) := D → K × K

def AllConstituentPairsDistinct {D K : Type*} (M : ConstituentOffsets D K) : Prop :=
  ∀ d, (M d).1 ≠ (M d).2

noncomputable def finiteUniformProbability {Ω : Type*} [Fintype Ω]
    (E : Ω → Prop) : ℝ :=
  (Nat.card {ω // E ω} : ℝ) / Nat.card Ω

noncomputable def distinctConstituentProbability (q : ℕ) : ℝ :=
  finiteUniformProbability
    (AllConstituentPairsDistinct (D := Fin (q + 1)) (K := Fin q))

end Balanced

end OAI
