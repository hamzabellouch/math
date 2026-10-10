import OAI.Computability.PerfectCompleteness.Algebra.BucketMatrixResampling
import OAI.Computability.PerfectCompleteness.Decoding.CollisionAveragingLemmas
import OAI.Computability.PerfectCompleteness.Decoding.RepresentativeBucketCollisionLemmas
import OAI.Computability.PerfectCompleteness.Foundations.QuarterBalanceLemmas

namespace OAI


namespace PerfectCompleteness.BucketUsefulCollision

noncomputable section

open scoped Classical
open ClauseSupport MixedSupport
open UniqueGamesTheorem.Foundations.Games
open BucketSampler (F2 Direction Tape)

section Product

variable {H : Type*} {ℓ : Nat}

def fill (a : Direction ℓ)
    (b : FiniteProductSplit.Others (Ω := fun _ : Direction ℓ => H) a)
    (h : H) : Tape ℓ H :=
  fun d => if hd : d = a then h else b ⟨d, hd⟩

@[simp] theorem fill_self (a : Direction ℓ)
    (b : FiniteProductSplit.Others (Ω := fun _ : Direction ℓ => H) a)
    (h : H) : fill a b h a = h := by
  simp [fill]

theorem fill_update (a : Direction ℓ)
    (b : FiniteProductSplit.Others (Ω := fun _ : Direction ℓ => H) a)
    (h h' : H) : Function.update (fill a b h) a h' = fill a b h' := by
  funext d
  by_cases hd : d = a
  · subst d
    simp [fill]
  · simp only [Function.update_of_ne hd, fill, dite_eq_right hd]

theorem fill_others (a : Direction ℓ) (t : Tape ℓ H) :
    fill a (FiniteProductSplit.others a t) (t a) = t := by
  funext d
  by_cases hd : d = a
  · subst d
    simp [fill]
  · simp only [fill, dite_eq_right hd, FiniteProductSplit.others]

theorem fill_others_update (a : Direction ℓ) (t : Tape ℓ H) (h : H) :
    fill a (FiniteProductSplit.others a t) h = Function.update t a h := by
  rw [← fill_update a (FiniteProductSplit.others a t) (t a) h, fill_others]

private theorem probability_eq_expectation {A : Type*} [Fintype A]
    (μ : FiniteDistribution A) (event : A → Bool) :
    μ.probability event = μ.expectation (fun x => if event x then 1 else 0) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    mul_ite, mul_one, mul_zero]

variable [Fintype H]

theorem probability_background_first (μ : FiniteDistribution H)
    (a : Direction ℓ) (event : Tape ℓ H → Bool) :
    (BucketSampler.tapeLaw ℓ μ).probability event =
      (FiniteProductSplit.otherLaw (fun _ : Direction ℓ => μ) a).expectation
        (fun b => μ.probability (fun h => event (fill a b h))) := by
  have h := FiniteProductSplit.expectation_background_first
    (fun _ : Direction ℓ => μ) a
    (fun h b => if event (fill a b h) then (1 : ℝ) else 0)
  simpa only [fill_others, ← probability_eq_expectation, BucketSampler.tapeLaw] using h

theorem probability_resampling (μ : FiniteDistribution H)
    (a : Direction ℓ) (event : Tape ℓ H → Tape ℓ H → Bool) :
    ((BucketSampler.tapeLaw ℓ μ).product μ).probability
        (fun z => event z.1 (Function.update z.1 a z.2)) =
      (FiniteProductSplit.otherLaw (fun _ : Direction ℓ => μ) a).expectation
        (fun b => (μ.product μ).probability
          (fun z => event (fill a b z.1) (fill a b z.2))) := by
  have h := FiniteProductSplit.resampling_expectation
    (fun _ : Direction ℓ => μ) a
    (fun b h h' => if event (fill a b h) (fill a b h') then (1 : ℝ) else 0)
  simp only [fill_others] at h
  simpa only [fill_others_update, ← probability_eq_expectation, BucketSampler.tapeLaw] using h

end Product


variable {n ℓ : Nat} {Z : Type*}
  (slots : Fin n → Slot) (V : Submodule F2 (Assignment slots → F2))
  (other : Assignment slots → Z) (σ : KeyStrategy.Strategy n)
  (W : Submodule F2 V) (s : (V ⧸ W) →ₗ[F2] V)

theorem assembledMatrix_fill (a : Direction ℓ)
    (b : FiniteProductSplit.Others (Ω := fun _ : Direction ℓ => V) a) (h : V) :
    BucketMatrixResampling.assembledMatrix V ℓ (fill a b h) =
      EvaluationMatrix.shift V
        (BucketMatrixResampling.assembledMatrix V ℓ (fill a b 0)) a.val h := by
  have he := BucketMatrixResampling.assembledMatrix_update V ℓ (fill a b 0) a h
  rw [fill_update] at he
  simpa only [fill_self, sub_zero] using he

variable [Fintype V] [Finite Z]

theorem collision_probability_lower_bound
    (hs : W.mkQ.comp s = LinearMap.id)
    (hW : RepresentativeMatrixTable.Determined slots V other W)
    (μ : FiniteDistribution V)
    (useful : (Module.Dual F2 (V ⧸ W) →ₗ[F2] (Fin ℓ → F2)) → Prop)
    (a : Direction ℓ) :
    (BucketSampler.tapeLaw ℓ μ).probability
        (fun t => decide (CanonicalMatrixTable.Accepts slots V other σ a.val
          (BucketMatrixResampling.assembledMatrix V ℓ t)) &&
          (RepresentativeMatrixTable.partialTable slots V other σ W s useful
            (MatrixRowQuotient.projectMatrix W
              (BucketMatrixResampling.assembledMatrix V ℓ t))).isSome) ^ 2 / 2 ≤
      ((BucketSampler.tapeLaw ℓ μ).product μ).probability
        (fun z => TwoResponseCollision.collision
          (RepresentativeMatrixTable.partialTable slots V other σ W s useful)
          (MatrixRowQuotient.projectMatrix W
            (BucketMatrixResampling.assembledMatrix V ℓ z.1),
          MatrixRowQuotient.projectMatrix W
            (BucketMatrixResampling.assembledMatrix V ℓ (Function.update z.1 a z.2)))) := by
  let f := RepresentativeMatrixTable.partialTable slots V other σ W s useful
  let good : Tape ℓ V → Bool := fun t =>
    decide (CanonicalMatrixTable.Accepts slots V other σ a.val
      (BucketMatrixResampling.assembledMatrix V ℓ t)) &&
      (f (MatrixRowQuotient.projectMatrix W
        (BucketMatrixResampling.assembledMatrix V ℓ t))).isSome
  let collision : Tape ℓ V → Tape ℓ V → Bool := fun t t' =>
    TwoResponseCollision.collision f
      (MatrixRowQuotient.projectMatrix W (BucketMatrixResampling.assembledMatrix V ℓ t),
        MatrixRowQuotient.projectMatrix W (BucketMatrixResampling.assembledMatrix V ℓ t'))
  change (BucketSampler.tapeLaw ℓ μ).probability good ^ 2 / 2 ≤
    ((BucketSampler.tapeLaw ℓ μ).product μ).probability
      (fun z => collision z.1 (Function.update z.1 a z.2))
  rw [probability_background_first μ a good, probability_resampling μ a collision]
  apply CollisionAveraging.average_square_bound
  intro b
  have hgood : (fun h : V => good (fill a b h)) =
      TwoResponseCollision.goodDefined
        (RepresentativeBucketCollision.bucketTable slots V other σ W s useful a.val
          (BucketMatrixResampling.assembledMatrix V ℓ (fill a b 0)))
        (RepresentativeBucketCollision.bucketAccepted slots V other σ a.val
          (BucketMatrixResampling.assembledMatrix V ℓ (fill a b 0))) := by
    funext h
    dsimp only [good, f, TwoResponseCollision.goodDefined,
      RepresentativeBucketCollision.bucketTable, RepresentativeBucketCollision.bucketAccepted]
    simp only [assembledMatrix_fill slots V a b h]
  have htable (h : V) :
      f (MatrixRowQuotient.projectMatrix W
        (BucketMatrixResampling.assembledMatrix V ℓ (fill a b h))) =
      RepresentativeBucketCollision.bucketTable slots V other σ W s useful a.val
        (BucketMatrixResampling.assembledMatrix V ℓ (fill a b 0)) h := by
    dsimp only [f, RepresentativeBucketCollision.bucketTable]
    rw [assembledMatrix_fill slots V a b h]
  have hcollision :
      (fun z : V × V => collision (fill a b z.1) (fill a b z.2)) =
      TwoResponseCollision.collision
        (RepresentativeBucketCollision.bucketTable slots V other σ W s useful a.val
          (BucketMatrixResampling.assembledMatrix V ℓ (fill a b 0))) := by
    exact congrArg (fun g : V → Option ((Fin ℓ → F2) × Z) =>
      TwoResponseCollision.collision g) (funext htable)
  rw [hgood, hcollision]
  exact RepresentativeBucketCollision.collision_probability_lower_bound
    slots V other σ W s hs hW μ useful a.val a.property
      (BucketMatrixResampling.assembledMatrix V ℓ (fill a b 0))

end
end PerfectCompleteness.BucketUsefulCollision

end OAI
