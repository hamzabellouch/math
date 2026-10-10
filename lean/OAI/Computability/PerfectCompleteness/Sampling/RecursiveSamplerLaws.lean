import OAI.Computability.PerfectCompleteness.Algebra.UniformLinearImage

namespace OAI

section

namespace PerfectCompleteness.FiniteProduct

open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

theorem eval_pushforward (P : (i : I) → FiniteDistribution (Ω i)) (i : I) :
    (law P).pushforward (fun x => x i) = P i := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro a
  calc
    _ = (law P).expectation (fun x => if x i = a then 1 else 0) := by
      simp [FiniteDistribution.pushforward, FiniteDistribution.expectation, mul_ite]
    _ = (P i).expectation (fun b => if b = a then 1 else 0) :=
      expectation_eval P i (fun b => if b = a then (1 : ℝ) else 0)
    _ = _ := by simp [FiniteDistribution.expectation, mul_ite]

end
end PerfectCompleteness.FiniteProduct

end

end OAI
