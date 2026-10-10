import OAI.Computability.PerfectCompleteness.Construction.BucketQuotientAgreement

namespace OAI

section

namespace PerfectCompleteness.BucketFullAgreement

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open BucketSampler (F2 Direction Tape)
open PartialTableInverse (definedEquality nonzeroAgreement)

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {Ω Y : Type*} [Fintype Y]
  (V : Submodule F2 (Ω → F2)) [Fintype V] [FiniteDimensional F2 V]
  (ℓ : Nat)

abbrev Sample := Direction ℓ × (Tape ℓ V × V)

def law [Nonempty (Direction ℓ)] : FiniteDistribution (Sample V ℓ) :=
  (FiniteDistribution.uniform (Direction ℓ)).product
    ((BucketSampler.tapeLaw ℓ (FiniteDistribution.uniform V)).product
      (FiniteDistribution.uniform V))

def pair (sample : Sample V ℓ) :
    BucketMatrixResampling.Matrix V ℓ × BucketMatrixResampling.Matrix V ℓ :=
  (BucketMatrixResampling.assembledMatrix V ℓ sample.2.1,
    BucketMatrixResampling.assembledMatrix V ℓ
      (Function.update sample.2.1 sample.1 sample.2.2))

private theorem expectation_uniform_eq_expect {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℝ) :
    (FiniteDistribution.uniform A).expectation f = 𝔼 x : A, f x := by
  rw [FiniteDistribution.expectation_uniform, Fintype.expect_eq_sum_div_card]

theorem collision_probability [Nonempty (Direction ℓ)]
    (f : BucketMatrixResampling.Matrix V ℓ → Option Y) :
    (law V ℓ).probability (fun sample => TwoResponseCollision.collision f (pair V ℓ sample)) =
      nonzeroAgreement f := by
  rw [law, BucketQuotientAgreement.probability_collision_eq_expectation,
    FiniteDistribution.expectation_product, expectation_uniform_eq_expect]
  calc
    _ = FiniteRangeInverse.agreement f := by
      unfold FiniteRangeInverse.agreement
      refine Finset.expect_congr (ι := Direction ℓ) ?_ ?_
      · ext a
        simp only [Finset.mem_univ]
      intro a _
      have hevent := BucketMatrixResampling.uniform_resampled_event_probability V ℓ a
        (TwoResponseCollision.collision f)
      rw [BucketQuotientAgreement.probability_collision_eq_expectation,
        BucketQuotientAgreement.probability_collision_eq_expectation,
        FiniteDistribution.expectation_product] at hevent
      simpa only [FiniteDistribution.expectation_product, expectation_uniform_eq_expect,
        pair, EvaluationMatrix.shift, FiniteRangeInverse.matrixStep] using hevent
    _ = nonzeroAgreement f := FiniteRangeInverse.agreement_eq_nonzeroAgreement f

end
end PerfectCompleteness.BucketFullAgreement

end

end OAI
