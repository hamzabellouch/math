import OAI.Computability.PerfectCompleteness.Algebra.BucketMatrixResampling
import OAI.Computability.PerfectCompleteness.Decoding.TwoResponseCollisionLemmas
import OAI.Computability.PerfectCompleteness.Foundations.QuotientTableAgreementLemmas

namespace OAI

section

namespace PerfectCompleteness.BucketQuotientAgreement

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open BucketSampler (F2 Direction Tape)
open PartialTableInverse (definedEquality nonzeroAgreement)

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

theorem collision_indicator_eq {A Y : Type*} [Fintype A] [Fintype Y]
    (f : A → Option Y) (x y : A) :
    (if TwoResponseCollision.collision f (x, y) then (1 : ℝ) else 0) =
      definedEquality f x y := by
  simp [TwoResponseCollision.collision, definedEquality]

theorem probability_collision_eq_expectation {A B Y : Type*}
    [Fintype A] [Fintype B] [Fintype Y]
    (μ : FiniteDistribution A) (f : B → Option Y) (p q : A → B) :
    μ.probability (fun x => TwoResponseCollision.collision f (p x, q x)) =
      μ.expectation (fun x => definedEquality f (p x) (q x)) := by
  unfold FiniteDistribution.probability FiniteDistribution.expectation
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : ∃ y, f (p x) = some y ∧ f (q x) = some y <;>
    simp [TwoResponseCollision.collision, definedEquality, h]

private theorem expectation_uniform_eq_expect {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℝ) :
    (FiniteDistribution.uniform A).expectation f = 𝔼 x : A, f x := by
  rw [FiniteDistribution.expectation_uniform, Fintype.expect_eq_sum_div_card]

variable {Ω Y : Type*} [Fintype Y]
  (V : Submodule F2 (Ω → F2)) [Fintype V] [FiniteDimensional F2 V]
  (ℓ : Nat) (W : Submodule F2 V)

def directionCollision
    (f : (Module.Dual F2 (V ⧸ W) →ₗ[F2] (Fin ℓ → F2)) → Option Y)
    (a : Direction ℓ) : ℝ :=
  ((BucketSampler.tapeLaw ℓ (FiniteDistribution.uniform V)).product
    (FiniteDistribution.uniform V)).probability
      (fun p => TwoResponseCollision.collision f
        (MatrixRowQuotient.projectMatrix W (BucketMatrixResampling.assembledMatrix V ℓ p.1),
          MatrixRowQuotient.projectMatrix W
            (BucketMatrixResampling.assembledMatrix V ℓ (Function.update p.1 a p.2))))

theorem directionCollision_eq
    (f : (Module.Dual F2 (V ⧸ W) →ₗ[F2] (Fin ℓ → F2)) → Option Y)
    (a : Direction ℓ) :
    directionCollision V ℓ W f a =
      𝔼 X : Module.Dual F2 V →ₗ[F2] (Fin ℓ → F2), 𝔼 h : V,
        definedEquality f (MatrixRowQuotient.projectMatrix W X)
          (MatrixRowQuotient.projectMatrix W (EvaluationMatrix.shift V X a.val h)) := by
  unfold directionCollision
  rw [BucketMatrixResampling.uniform_resampled_event_probability V ℓ a
    (fun p => TwoResponseCollision.collision f
      (MatrixRowQuotient.projectMatrix W p.1, MatrixRowQuotient.projectMatrix W p.2))]
  rw [probability_collision_eq_expectation, FiniteDistribution.expectation_product]
  simp only [expectation_uniform_eq_expect]

def agreement
    (f : (Module.Dual F2 (V ⧸ W) →ₗ[F2] (Fin ℓ → F2)) → Option Y) : ℝ :=
  𝔼 a : Direction ℓ, directionCollision V ℓ W f a

theorem agreement_eq_projectedAgreement
    (f : (Module.Dual F2 (V ⧸ W) →ₗ[F2] (Fin ℓ → F2)) → Option Y) :
    agreement V ℓ W f = QuotientTableAgreement.projectedAgreement W f := by
  unfold agreement QuotientTableAgreement.projectedAgreement
  refine Finset.expect_congr (ι := Direction ℓ) ?_ ?_
  · ext a
    simp only [Finset.mem_univ]
  · intro a _
    exact directionCollision_eq V ℓ W f a

theorem agreement_eq_nonzeroAgreement
    (f : (Module.Dual F2 (V ⧸ W) →ₗ[F2] (Fin ℓ → F2)) → Option Y) :
    agreement V ℓ W f = nonzeroAgreement f := by
  rw [agreement_eq_projectedAgreement,
    QuotientTableAgreement.projectedAgreement_eq_nonzeroAgreement]

theorem uniform_bucket_collision_probability [Nonempty (Direction ℓ)]
    (f : (Module.Dual F2 (V ⧸ W) →ₗ[F2] (Fin ℓ → F2)) → Option Y) :
    ((FiniteDistribution.uniform (Direction ℓ)).product
      ((BucketSampler.tapeLaw ℓ (FiniteDistribution.uniform V)).product
        (FiniteDistribution.uniform V))).probability
      (fun p => TwoResponseCollision.collision f
        (MatrixRowQuotient.projectMatrix W
          (BucketMatrixResampling.assembledMatrix V ℓ p.2.1),
        MatrixRowQuotient.projectMatrix W
          (BucketMatrixResampling.assembledMatrix V ℓ
            (Function.update p.2.1 p.1 p.2.2)))) = nonzeroAgreement f := by
  rw [probability_collision_eq_expectation, FiniteDistribution.expectation_product,
    expectation_uniform_eq_expect]
  calc
    _ = agreement V ℓ W f := by
      unfold agreement
      apply Finset.expect_congr rfl
      intro a _
      exact (probability_collision_eq_expectation
        ((BucketSampler.tapeLaw ℓ (FiniteDistribution.uniform V)).product
          (FiniteDistribution.uniform V)) f
        (fun p => MatrixRowQuotient.projectMatrix W
          (BucketMatrixResampling.assembledMatrix V ℓ p.1))
        (fun p => MatrixRowQuotient.projectMatrix W
          (BucketMatrixResampling.assembledMatrix V ℓ (Function.update p.1 a p.2)))).symm
    _ = nonzeroAgreement f := agreement_eq_nonzeroAgreement V ℓ W f

end
end PerfectCompleteness.BucketQuotientAgreement

end

end OAI
