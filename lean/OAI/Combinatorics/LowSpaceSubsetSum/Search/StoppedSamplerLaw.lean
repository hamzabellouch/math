import OAI.Combinatorics.LowSpaceSubsetSum.Counting.RejectionSamplerCoupling

namespace OAI

/-! # The law of a dependent sampler that stops on exhaustion

Only an actual successful first value selects the next distribution.
The ideal completion of a failed first call disappears from this formula.
-/

noncomputable section
namespace LowSpaceSubsetSum.StoppedSamplerLaw

open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {α : Type} [Fintype α]

def nextProbability (B : α → Type) [∀ a, Fintype (B a)]
    (T : ∀ a, SamplerCoupling (B a)) (P : Option (Sigma B) → Prop) : Option α → ℝ
  | none => if P none then 1 else 0
  | some a => (T a).boundedLaw.probability (fun b => P (b.map (fun v => ⟨a,v⟩)))

theorem bind_probability (S : SamplerCoupling α)
    (B : α → Type) [∀ a, Fintype (B a)] (T : ∀ a, SamplerCoupling (B a))
    (P : Option (Sigma B) → Prop) :
    (S.bind B T).boundedLaw.probability P =
      S.boundedLaw.expectation (nextProbability B T P) := by
  classical
  rw [SamplerCoupling.boundedLaw, FiniteLaw.map_probability]
  change (S.law.bind (fun s => (T (S.ideal s)).Seed)
    (fun s => (T (S.ideal s)).law)).probability
      (fun z => P ((S.bind B T).bounded z)) = _
  rw [FiniteLaw.bind_probability, SamplerCoupling.boundedLaw, FiniteLaw.map_expectation]
  unfold FiniteLaw.expectation
  apply Finset.sum_congr rfl
  intro s _
  apply congrArg (fun x => S.law.mass s*x)
  cases hs : S.bounded s with
  | none =>
    simp only [SamplerCoupling.bind, hs, ↓reduceIte, nextProbability]
    by_cases hp : P none
    · simp only [FiniteLaw.probability, hp, ↓reduceIte, (T (S.ideal s)).law.total]
    · simp only [FiniteLaw.probability, hp, ↓reduceIte, Finset.sum_const_zero]
  | some a =>
    have hi : S.ideal s = a := by
      rcases S.agrees s with hf | he
      · rw [hs] at hf
        contradiction
      · exact Option.some.inj (he.symm.trans hs)
    subst a
    simp only [SamplerCoupling.bind, hs, Option.some_ne_none, ↓reduceIte, nextProbability,
      SamplerCoupling.boundedLaw, FiniteLaw.map_probability]

end LowSpaceSubsetSum.StoppedSamplerLaw

end

end OAI
