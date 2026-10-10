import OAI.Computability.PerfectCompleteness.Sampling.BucketResamplingLaw
import OAI.Computability.PerfectCompleteness.Sampling.BucketUniformLemmas

namespace OAI


namespace PerfectCompleteness.BucketMatrixResampling

noncomputable section

open scoped Classical
open UniqueGamesTheorem.Foundations.Games
open BucketSampler (F2 Direction Tape)

variable {Ω : Type*} (V : Submodule F2 (Ω → F2))

abbrev Matrix (ℓ : Nat) := Module.Dual F2 V →ₗ[F2] (Fin ℓ → F2)

def assembledMatrix (ℓ : Nat) (t : Tape ℓ V) : Matrix V ℓ :=
  EvaluationMatrix.ofRows V (BucketSampler.evaluate ℓ (id : V → V) t)

theorem assembledMatrix_update (ℓ : Nat) (t : Tape ℓ V)
    (a : Direction ℓ) (new : V) :
    assembledMatrix V ℓ (Function.update t a new) =
      EvaluationMatrix.shift V (assembledMatrix V ℓ t) a.val (new - t a) := by
  unfold assembledMatrix
  rw [BucketSampler.evaluate_update]
  apply LinearMap.ext
  intro q
  funext i
  change q (BucketSampler.evaluate ℓ (id : V → V) t i + a.val i • (new - t a)) =
    q (BucketSampler.evaluate ℓ (id : V → V) t i) + q (new - t a) * a.val i
  simp only [map_add, map_smul, smul_eq_mul, mul_comm]

private theorem pushforward_id {A : Type*} [Fintype A] (μ : FiniteDistribution A) :
    μ.pushforward (fun a => a) = μ := by
  apply FiniteDistribution.eq_of_weight_eq
  intro a
  simp [FiniteDistribution.pushforward]


variable (ℓ : Nat) [Fintype V] [Fintype (Matrix V ℓ)]

theorem matrix_difference_law (μ : FiniteDistribution (Tape ℓ V)) (a : Direction ℓ) :
    (μ.product (FiniteDistribution.uniform V)).pushforward
        (fun p => (assembledMatrix V ℓ p.1, p.2 - p.1 a)) =
      (μ.pushforward (assembledMatrix V ℓ)).product (FiniteDistribution.uniform V) := by
  rw [UniformDifference.observed_difference_law μ (fun t => t a)
    (assembledMatrix V ℓ)]
  have hp := FiniteDistribution.product_pushforward μ
    (FiniteDistribution.uniform V) (assembledMatrix V ℓ) (id : V → V)
  have hi : (FiniteDistribution.uniform V).pushforward (id : V → V) =
      FiniteDistribution.uniform V :=
    pushforward_id (FiniteDistribution.uniform V)
  rw [hi] at hp
  simpa only [id_eq] using hp

theorem resampled_matrix_pair_law (μ : FiniteDistribution (Tape ℓ V)) (a : Direction ℓ) :
    (μ.product (FiniteDistribution.uniform V)).pushforward
        (fun p => (assembledMatrix V ℓ p.1,
          assembledMatrix V ℓ (Function.update p.1 a p.2))) =
      ((μ.pushforward (assembledMatrix V ℓ)).product (FiniteDistribution.uniform V)).pushforward
        (fun p => (p.1, EvaluationMatrix.shift V p.1 a.val p.2)) := by
  have h := congrArg
    (fun ν : FiniteDistribution (Matrix V ℓ × V) => ν.pushforward
      (fun p => (p.1, EvaluationMatrix.shift V p.1 a.val p.2)))
    (matrix_difference_law V ℓ μ a)
  rw [FiniteDistribution.pushforward_comp] at h
  simpa only [assembledMatrix_update] using h

variable [FiniteDimensional F2 V]

theorem uniform_assembledMatrix_law :
    (BucketSampler.tapeLaw ℓ (FiniteDistribution.uniform V)).pushforward
        (assembledMatrix V ℓ) = FiniteDistribution.uniform (Matrix V ℓ) :=
  BucketUniform.uniform_matrix_law V ℓ

theorem uniform_matrix_difference_law (a : Direction ℓ) :
    ((BucketSampler.tapeLaw ℓ (FiniteDistribution.uniform V)).product
        (FiniteDistribution.uniform V)).pushforward
        (fun p => (assembledMatrix V ℓ p.1, p.2 - p.1 a)) =
      (FiniteDistribution.uniform (Matrix V ℓ)).product (FiniteDistribution.uniform V) := by
  rw [matrix_difference_law, uniform_assembledMatrix_law]

theorem uniform_resampled_matrix_pair_law (a : Direction ℓ) :
    ((BucketSampler.tapeLaw ℓ (FiniteDistribution.uniform V)).product
        (FiniteDistribution.uniform V)).pushforward
        (fun p => (assembledMatrix V ℓ p.1,
          assembledMatrix V ℓ (Function.update p.1 a p.2))) =
      ((FiniteDistribution.uniform (Matrix V ℓ)).product
        (FiniteDistribution.uniform V)).pushforward
          (fun p => (p.1, EvaluationMatrix.shift V p.1 a.val p.2)) := by
  rw [resampled_matrix_pair_law, uniform_assembledMatrix_law]

theorem uniform_resampled_event_probability (a : Direction ℓ)
    (event : Matrix V ℓ × Matrix V ℓ → Bool) :
    ((BucketSampler.tapeLaw ℓ (FiniteDistribution.uniform V)).product
        (FiniteDistribution.uniform V)).probability
        (fun p => event (assembledMatrix V ℓ p.1,
          assembledMatrix V ℓ (Function.update p.1 a p.2))) =
      ((FiniteDistribution.uniform (Matrix V ℓ)).product
        (FiniteDistribution.uniform V)).probability
          (fun p => event (p.1, EvaluationMatrix.shift V p.1 a.val p.2)) := by
  have h := congrArg (fun ν => FiniteDistribution.probability ν event)
    (uniform_resampled_matrix_pair_law V ℓ a)
  simpa only [FiniteDistribution.probability_pushforward] using h

end
end PerfectCompleteness.BucketMatrixResampling

end OAI
