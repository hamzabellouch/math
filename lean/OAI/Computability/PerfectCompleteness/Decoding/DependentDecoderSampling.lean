import OAI.Computability.PerfectCompleteness.Decoding.TwoResponseCollisionLemmas
import OAI.Computability.PerfectCompleteness.Reduction.CompletionSoundness
import OAI.Computability.PerfectCompleteness.Sampling.RecursiveSamplerLaws

namespace OAI

section

namespace PerfectCompleteness.DependentDecoderSampling

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {Q₁ Q₂ E : Type*} [Fintype Q₁] [Fintype Q₂] [Fintype E]
  [DecidableEq Q₁] [DecidableEq Q₂]
  {A : Q₁ → Type*} {B : Q₂ → Type*}
  [∀ q, Fintype (A q)] [∀ q, Fintype (B q)]

abbrev Seed (A : Q₁ → Type*) (B : Q₂ → Type*) :=
  ((q : Q₁) → A q) × ((q : Q₂) → B q)

def seedLaw (leftKernel : (q : Q₁) → FiniteDistribution (A q))
    (rightKernel : (q : Q₂) → FiniteDistribution (B q)) :
    FiniteDistribution (Seed A B) :=
  (FiniteProduct.law leftKernel).product (FiniteProduct.law rightKernel)

theorem read_law (leftKernel : (q : Q₁) → FiniteDistribution (A q))
    (rightKernel : (q : Q₂) → FiniteDistribution (B q)) (q₁ : Q₁) (q₂ : Q₂) :
    (seedLaw leftKernel rightKernel).pushforward (fun seed => (seed.1 q₁, seed.2 q₂)) =
      (leftKernel q₁).product (rightKernel q₂) := by
  have h := FiniteDistribution.product_pushforward
    (FiniteProduct.law leftKernel) (FiniteProduct.law rightKernel)
    (fun table : (q : Q₁) → A q => table q₁)
    (fun table : (q : Q₂) → B q => table q₂)
  rw [FiniteProduct.eval_pushforward, FiniteProduct.eval_pushforward] at h
  exact h

def sampleLaw (μ : FiniteDistribution E) (left : E → Q₁) (right : E → Q₂)
    (leftKernel : (q : Q₁) → FiniteDistribution (A q))
    (rightKernel : (q : Q₂) → FiniteDistribution (B q)) :
    FiniteDistribution (Σ e : E, A (left e) × B (right e)) :=
  CompletionSoundness.sigmaLaw μ (fun e => (leftKernel (left e)).product (rightKernel (right e)))

theorem sample_probability_eq (μ : FiniteDistribution E) (left : E → Q₁) (right : E → Q₂)
    (leftKernel : (q : Q₁) → FiniteDistribution (A q))
    (rightKernel : (q : Q₂) → FiniteDistribution (B q))
    (event : (e : E) → A (left e) → B (right e) → Bool) :
    (sampleLaw μ left right leftKernel rightKernel).probability
        (fun x => event x.1 x.2.1 x.2.2) =
      (seedLaw leftKernel rightKernel).expectation
        (fun seed => μ.probability (fun e => event e (seed.1 (left e)) (seed.2 (right e)))) := by
  rw [sampleLaw, CompletionSoundness.sigmaLaw_probability]
  calc
    _ = μ.expectation (fun e => (seedLaw leftKernel rightKernel).probability
        (fun seed => event e (seed.1 (left e)) (seed.2 (right e)))) := by
      apply FiniteDistribution.expectation_congr
      intro e
      have h := FiniteDistribution.probability_pushforward
        (seedLaw leftKernel rightKernel) (fun seed => (seed.1 (left e), seed.2 (right e)))
        (fun answer => event e answer.1 answer.2)
      rw [read_law] at h
      exact h
    _ = μ.expectation (fun e => (seedLaw leftKernel rightKernel).expectation
        (fun seed => if event e (seed.1 (left e)) (seed.2 (right e)) then 1 else 0)) := by
      simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
        mul_ite, mul_one, mul_zero]
    _ = (seedLaw leftKernel rightKernel).expectation (fun seed => μ.expectation
        (fun e => if event e (seed.1 (left e)) (seed.2 (right e)) then 1 else 0)) :=
      FiniteDistribution.expectation_comm μ (seedLaw leftKernel rightKernel) _
    _ = _ := by
      simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
        mul_ite, mul_one, mul_zero]

theorem probability_le_of_supported_seeds
    (μ : FiniteDistribution E) (left : E → Q₁) (right : E → Q₂)
    (leftKernel : (q : Q₁) → FiniteDistribution (A q))
    (rightKernel : (q : Q₂) → FiniteDistribution (B q))
    (event : (e : E) → A (left e) → B (right e) → Bool) (bound : ℝ)
    (hbound : ∀ seed, (seedLaw leftKernel rightKernel).weight seed ≠ 0 →
      μ.probability (fun e => event e (seed.1 (left e)) (seed.2 (right e))) ≤ bound) :
    (sampleLaw μ left right leftKernel rightKernel).probability
      (fun x => event x.1 x.2.1 x.2.2) ≤ bound := by
  rw [sample_probability_eq]
  exact DecoderTableAdmissibility.expectation_le_of_support _ _ bound hbound

theorem supported_left (leftKernel : (q : Q₁) → FiniteDistribution (A q))
    (rightKernel : (q : Q₂) → FiniteDistribution (B q))
    (seed : Seed A B) (hs : (seedLaw leftKernel rightKernel).weight seed ≠ 0) (q : Q₁) :
    (leftKernel q).weight (seed.1 q) ≠ 0 := by
  intro hq
  apply hs
  have hz : (FiniteProduct.law leftKernel).weight seed.1 = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ q) hq
  change (FiniteProduct.law leftKernel).weight seed.1 *
    (FiniteProduct.law rightKernel).weight seed.2 = 0
  rw [hz, zero_mul]

theorem supported_right (leftKernel : (q : Q₁) → FiniteDistribution (A q))
    (rightKernel : (q : Q₂) → FiniteDistribution (B q))
    (seed : Seed A B) (hs : (seedLaw leftKernel rightKernel).weight seed ≠ 0) (q : Q₂) :
    (rightKernel q).weight (seed.2 q) ≠ 0 := by
  intro hq
  apply hs
  have hz : (FiniteProduct.law rightKernel).weight seed.2 = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ q) hq
  change (FiniteProduct.law leftKernel).weight seed.1 *
    (FiniteProduct.law rightKernel).weight seed.2 = 0
  rw [hz, mul_zero]

end
end PerfectCompleteness.DependentDecoderSampling

end

end OAI
