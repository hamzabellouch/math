import OAI.Computability.PerfectCompleteness.Sampling.BucketSampler
import OAI.Computability.PerfectCompleteness.Sampling.UniformDifference

namespace OAI

section

namespace PerfectCompleteness.BucketResamplingLaw

noncomputable section

open scoped Classical
open UniqueGamesTheorem.Foundations.Games
open BucketSampler (F2 Direction Tape)

variable {H : Type*} [AddCommGroup H] [Module F2 H] [Fintype H]

private theorem pushforward_id {A : Type*} [Fintype A] (μ : FiniteDistribution A) :
    μ.pushforward (fun a => a) = μ := by
  apply FiniteDistribution.eq_of_weight_eq
  intro a
  simp [FiniteDistribution.pushforward]

theorem assembled_difference_law (ℓ : Nat) (μ : FiniteDistribution (Tape ℓ H))
    (a : Direction ℓ) :
    (μ.product (FiniteDistribution.uniform H)).pushforward
        (fun p => (BucketSampler.evaluate ℓ id p.1, p.2 - p.1 a)) =
      (μ.pushforward (BucketSampler.evaluate ℓ id)).product (FiniteDistribution.uniform H) := by
  rw [UniformDifference.observed_difference_law μ (fun t => t a)
    (BucketSampler.evaluate ℓ id)]
  have hp := FiniteDistribution.product_pushforward μ (FiniteDistribution.uniform H)
    (BucketSampler.evaluate ℓ (id : H → H)) (id : H → H)
  have hi : (FiniteDistribution.uniform H).pushforward (id : H → H) =
      FiniteDistribution.uniform H := pushforward_id (FiniteDistribution.uniform H)
  rw [hi] at hp
  simpa only [id_eq] using hp

theorem resampled_array_pair_law (ℓ : Nat) (μ : FiniteDistribution (Tape ℓ H))
    (a : Direction ℓ) :
    (μ.product (FiniteDistribution.uniform H)).pushforward
        (fun p => (BucketSampler.evaluate ℓ id p.1,
          BucketSampler.evaluate ℓ id (Function.update p.1 a p.2))) =
      ((μ.pushforward (BucketSampler.evaluate ℓ id)).product
        (FiniteDistribution.uniform H)).pushforward
          (fun p => (p.1, p.1 + BucketSampler.rankOne a.val p.2)) := by
  have h := congrArg
    (fun ν : FiniteDistribution ((Fin ℓ → H) × H) => ν.pushforward
      (fun p => (p.1, p.1 + BucketSampler.rankOne a.val p.2)))
    (assembled_difference_law ℓ μ a)
  rw [FiniteDistribution.pushforward_comp] at h
  simpa only [BucketSampler.evaluate_update, id_eq] using h

theorem resampled_event_probability (ℓ : Nat) (μ : FiniteDistribution (Tape ℓ H))
    (a : Direction ℓ) (event : (Fin ℓ → H) × (Fin ℓ → H) → Bool) :
    (μ.product (FiniteDistribution.uniform H)).probability
        (fun p => event (BucketSampler.evaluate ℓ id p.1,
          BucketSampler.evaluate ℓ id (Function.update p.1 a p.2))) =
      ((μ.pushforward (BucketSampler.evaluate ℓ id)).product
        (FiniteDistribution.uniform H)).probability
          (fun p => event (p.1, p.1 + BucketSampler.rankOne a.val p.2)) := by
  have h := congrArg (fun ν => FiniteDistribution.probability ν event)
    (resampled_array_pair_law ℓ μ a)
  simpa only [FiniteDistribution.probability_pushforward] using h

end
end PerfectCompleteness.BucketResamplingLaw

end

end OAI
