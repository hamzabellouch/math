import OAI.Computability.PerfectCompleteness.Algebra.CanonicalMatrixTable
import OAI.Computability.PerfectCompleteness.Decoding.TwoResponseCollisionLemmas

namespace OAI

section

namespace PerfectCompleteness.CanonicalBucketCollision

noncomputable section

open scoped Classical
open ClauseSupport MixedSupport CanonicalKeys
open DirectionQuotient (F2)
open CanonicalMatrixTable TwoResponseCollision
open UniqueGamesTheorem.Foundations.Games

variable {n : Nat} {K Z : Type*} [AddCommGroup K] [Module F2 K]
  (slots : Fin n → Slot) (H : Submodule F2 (Assignment slots → F2))
  (other : Assignment slots → Z) (σ : KeyStrategy.Strategy n)

def bucketTable (useful : Matrix (K := K) slots H → Prop) (a : K) (X : Matrix (K := K) slots H)
    (h : H) : Option (K × Z) :=
  partialTable slots H other σ useful (EvaluationMatrix.shift H X a h)

def bucketAccepted (a : K) (X : Matrix (K := K) slots H) (h : H) : Bool :=
  decide (Accepts slots H other σ a (EvaluationMatrix.shift H X a h))

theorem bucketTable_eq_some_iff (useful : Matrix (K := K) slots H → Prop)
    (a : K) (X : Matrix (K := K) slots H) (h : H) (y : K × Z) :
    bucketTable slots H other σ useful a X h = some y ↔
      useful (EvaluationMatrix.shift H X a h) ∧
        response slots H other σ (EvaluationMatrix.shift H X a h) = y := by
  by_cases hu : useful (EvaluationMatrix.shift H X a h) <;>
    simp [bucketTable, partialTable, hu]

theorem collision_probability_lower_bound [Finite K] [Finite Z] [Fintype H]
    (μ : FiniteDistribution H) (useful : Matrix (K := K) slots H → Prop)
    (a : K) (ha : a ≠ 0) (X : Matrix (K := K) slots H) :
    μ.probability (goodDefined (bucketTable slots H other σ useful a X)
        (bucketAccepted slots H other σ a X)) ^ 2 / 2 ≤
      (μ.product μ).probability (collision (bucketTable slots H other σ useful a X)) := by
  let : Fintype K := Fintype.ofFinite K
  let : Fintype Z := Fintype.ofFinite Z
  apply collision_probability_ge_of_response_set μ
    (bucketTable slots H other σ useful a X) (bucketAccepted slots H other σ a X)
    (fun y => ∃ h : H,
      Accepts slots H other σ a (EvaluationMatrix.shift H X a h) ∧
        response slots H other σ (EvaluationMatrix.shift H X a h) = y)
  · exact card_accepted_responses_le_two slots H other σ a ha X
  · intro h y hgood hresponse
    refine ⟨h, ?_, ?_⟩
    · simpa only [bucketAccepted, decide_eq_true_eq] using hgood
    · exact ((bucketTable_eq_some_iff slots H other σ useful a X h y).mp hresponse).2

end
end PerfectCompleteness.CanonicalBucketCollision

end

end OAI
