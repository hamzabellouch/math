import OAI.Computability.PerfectCompleteness.Algebra.BilinearWitnessLemmas
import OAI.Computability.PerfectCompleteness.Decoding.CollisionAveragingLemmas
import OAI.Computability.PerfectCompleteness.Decoding.DecoderTableCoupling
import OAI.Computability.PerfectCompleteness.Decoding.TwoResponseCollisionLemmas
import OAI.Computability.PerfectCompleteness.Foundations.CoordinateReplacementLemmas
import OAI.Computability.PerfectCompleteness.Foundations.DependentPredictionDifferenceLemmas
import OAI.Computability.PerfectCompleteness.Foundations.OddListExtraction
import OAI.Computability.PerfectCompleteness.Reduction.CompletionSoundness
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas

namespace OAI


namespace PerfectCompleteness.MultiplicationFormInjective

noncomputable section

open scoped Classical
open PointwiseSpaces OddListExtraction
open UniqueGamesTheorem.Foundations.Games

variable {X : Type*} (H : Submodule F2 (X → F2))

theorem multiplicationForm_injective :
    Function.Injective (multiplicationForm H) := by
  intro z z' h
  apply (Submodule.linearMap_eq_iff_of_eq_span z z'
    (show squareSpace H =
      Submodule.span F2 {u | ∃ f ∈ H, ∃ g ∈ H, f * g = u} from rfl)).2
  rintro ⟨u, f, hf, g, hg, rfl⟩
  exact congrArg (fun F : H →ₗ[F2] H →ₗ[F2] F2 => F ⟨f, hf⟩ ⟨g, hg⟩) h

@[simp] theorem multiplicationForm_eq_iff
    (z z' : Module.Dual F2 (squareSpace H)) :
    multiplicationForm H z = multiplicationForm H z' ↔ z = z' :=
  (multiplicationForm_injective H).eq_iff

theorem optionMap_injective :
    Function.Injective (Option.map (multiplicationForm H)) :=
  Option.map_injective (multiplicationForm_injective H)

theorem definedEqual_map_of_injective {A B : Type*} (f : A → B)
    (hf : Function.Injective f) (a b : Option A) :
    DecoderTableCoupling.definedEqual (a.map f) (b.map f) =
      DecoderTableCoupling.definedEqual a b := by
  cases a <;> cases b <;>
    simp [DecoderTableCoupling.definedEqual, hf.eq_iff]

@[simp] theorem definedEqual_map
    (a b : Option (Module.Dual F2 (squareSpace H))) :
    DecoderTableCoupling.definedEqual (a.map (multiplicationForm H))
        (b.map (multiplicationForm H)) =
      DecoderTableCoupling.definedEqual a b :=
  definedEqual_map_of_injective _ (multiplicationForm_injective H) a b

@[simp] theorem fullCollision_map
    (a b : Option (Module.Dual F2 (squareSpace H))) :
    BilinearCollisionTransfer.fullCollision (a.map (multiplicationForm H))
        (b.map (multiplicationForm H)) =
      DecoderTableCoupling.definedEqual a b :=
  definedEqual_map H a b

@[simp] theorem collision_map {Ω : Type*}
    (answers : Ω → Option (Module.Dual F2 (squareSpace H))) (p : Ω × Ω) :
    TwoResponseCollision.collision (fun x => (answers x).map (multiplicationForm H)) p =
      TwoResponseCollision.collision answers p :=
  definedEqual_map H (answers p.1) (answers p.2)

theorem fullCollision_probability {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω)
    (first second : Ω → Option (Module.Dual F2 (squareSpace H))) :
    μ.probability (fun x => BilinearCollisionTransfer.fullCollision
        ((first x).map (multiplicationForm H))
        ((second x).map (multiplicationForm H))) =
      μ.probability (fun x => DecoderTableCoupling.definedEqual (first x) (second x)) := by
  apply congrArg μ.probability
  funext x
  exact fullCollision_map H (first x) (second x)

theorem collision_probability {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution (Ω × Ω))
    (answers : Ω → Option (Module.Dual F2 (squareSpace H))) :
    μ.probability (TwoResponseCollision.collision
        (fun x => (answers x).map (multiplicationForm H))) =
      μ.probability (TwoResponseCollision.collision answers) := by
  apply congrArg μ.probability
  funext p
  exact collision_map H answers p

end
end PerfectCompleteness.MultiplicationFormInjective


namespace PerfectCompleteness.SingleResponseResampling

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {B : Type*} [Fintype B]
  {Ω Y : B → Type*} [∀ b, Fintype (Ω b)] [∀ b, Fintype (Y b)]

def originalLaw (μ : FiniteDistribution B)
    (ν : (b : B) → FiniteDistribution (Ω b)) :=
  CompletionSoundness.sigmaLaw μ ν

def resampledLaw (μ : FiniteDistribution B)
    (ν : (b : B) → FiniteDistribution (Ω b)) :=
  CompletionSoundness.sigmaLaw μ (fun b => (ν b).product (ν b))

theorem probability_rectangle {A C : Type*} [Fintype A] [Fintype C]
    (μ : FiniteDistribution A) (ν : FiniteDistribution C)
    (p : A → Bool) (q : C → Bool) :
    (μ.product ν).probability (fun x => p x.1 && q x.2) =
      μ.probability p * ν.probability q := by
  unfold FiniteDistribution.probability
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  cases hp : p a <;> cases hq : q c <;> simp [FiniteDistribution.product, hp, hq]

theorem local_square_bound {A C : Type*} [Fintype A] [Fintype C]
    (ν : FiniteDistribution A) (f : A → Option C) (right : C) :
    ν.probability (fun x => decide (f x = some right)) ^ 2 ≤
      (ν.product ν).probability (TwoResponseCollision.collision f) := by
  rw [pow_two, ← probability_rectangle]
  apply FiniteDistribution.probability_mono
  intro x hx
  obtain ⟨hx₁, hx₂⟩ := Bool.and_eq_true_iff.mp hx
  exact decide_eq_true ⟨right, of_decide_eq_true hx₁, of_decide_eq_true hx₂⟩

theorem success_square_le_collision (μ : FiniteDistribution B)
    (ν : (b : B) → FiniteDistribution (Ω b))
    (f : (b : B) → Ω b → Option (Y b)) (right : (b : B) → Y b) :
    (originalLaw μ ν).probability
        (fun x => decide (f x.1 x.2 = some (right x.1))) ^ 2 ≤
      (resampledLaw μ ν).probability
        (fun x => TwoResponseCollision.collision (f x.1) x.2) := by
  unfold originalLaw resampledLaw
  rw [CompletionSoundness.sigmaLaw_probability,
    CompletionSoundness.sigmaLaw_probability]
  apply (CollisionAveraging.mean_square_le μ _).trans
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_left (local_square_bound (ν b) (f b) (right b))
    (μ.nonnegative b)

theorem success_square_le_event (μ : FiniteDistribution B)
    (ν : (b : B) → FiniteDistribution (Ω b))
    (f : (b : B) → Ω b → Option (Y b)) (right : (b : B) → Y b)
    (event : (Σ b, Ω b × Ω b) → Bool)
    (contains : ∀ b x y z, f b x = some z → f b y = some z →
      event ⟨b, x, y⟩ = true) :
    (originalLaw μ ν).probability
        (fun x => decide (f x.1 x.2 = some (right x.1))) ^ 2 ≤
      (resampledLaw μ ν).probability event := by
  apply (success_square_le_collision μ ν f right).trans
  apply FiniteDistribution.probability_mono
  intro x hx
  obtain ⟨z, hz₁, hz₂⟩ := of_decide_eq_true hx
  exact contains x.1 x.2.1 x.2.2 z hz₁ hz₂

end
end PerfectCompleteness.SingleResponseResampling


namespace PerfectCompleteness.SparseReplacement

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open CoordinateReplacement

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

def row (P Q : (i : I) → FiniteDistribution (Ω i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (i : I) :
    FiniteDistribution (Ω i) :=
  (ProjectionPosterior.bernoulli β hβ hβ').mixture
    (fun marked => if marked then Q i else P i)

omit [Fintype I] [DecidableEq I] in
theorem row_weight (P Q : (i : I) → FiniteDistribution (Ω i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (i : I) (a : Ω i) :
    (row P Q β hβ hβ' i).weight a =
      (1 - β) * (P i).weight a + β * (Q i).weight a := by
  simp [row, FiniteDistribution.mixture, ProjectionPosterior.bernoulli,
    add_comm]

def law (P Q : (i : I) → FiniteDistribution (Ω i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution ((i : I) → Ω i) :=
  FiniteProduct.law (row P Q β hβ hβ')

def markedLaw (P Q : (i : I) → FiniteDistribution (Ω i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution ((I → Bool) × ((i : I) → Ω i)) :=
  CleanConditioning.kernelJoint
    (FiniteProduct.law fun _ : I => ProjectionPosterior.bernoulli β hβ hβ')
    (fun mask => FiniteProduct.law fun i => if mask i then Q i else P i)

theorem markedLaw_marginal (P Q : (i : I) → FiniteDistribution (Ω i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (markedLaw P Q β hβ hβ').pushforward Prod.snd = law P Q β hβ hβ' := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  have hsum : ((markedLaw P Q β hβ hβ').pushforward Prod.snd).weight x =
      ∑ mask : I → Bool,
        (∏ i, (ProjectionPosterior.bernoulli β hβ hβ').weight (mask i)) *
          (∏ i, (if mask i then Q i else P i).weight (x i)) := by
    simp [markedLaw, FiniteDistribution.pushforward, CleanConditioning.kernelJoint,
      Fintype.sum_prod_type, FiniteProduct.law]
  rw [hsum]
  change (∑ mask : I → Bool,
      (∏ i, (ProjectionPosterior.bernoulli β hβ hβ').weight (mask i)) *
        (∏ i, (if mask i then Q i else P i).weight (x i))) =
    ∏ i, ∑ b : Bool, (ProjectionPosterior.bernoulli β hβ hβ').weight b *
      (if b then Q i else P i).weight (x i)
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i b =>
    (ProjectionPosterior.bernoulli β hβ hβ').weight b *
      (if b then Q i else P i).weight (x i))).symm

omit [Fintype I] [DecidableEq I] in

theorem ratio_reweight_eq (P Q : (i : I) → FiniteDistribution (Ω i))
    (support : ∀ i a, (P i).weight a = 0 → (Q i).weight a = 0) (i : I) :
    DensityVariation.reweight (P i) (ratio P Q i) (ratio_nonnegative P Q i)
      (ratio_mean_one_of_support P Q support i) = Q i := by
  apply FiniteDistribution.eq_of_weight_eq
  exact weight_mul_ratio_of_support P Q support i

theorem projectedLaw_eq (P Q : (i : I) → FiniteDistribution (Ω i))
    (support : ∀ i a, (P i).weight a = 0 → (Q i).weight a = 0)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    SparseProjection.projectedLaw P (ratio P Q) (ratio_nonnegative P Q)
      (ratio_mean_one_of_support P Q support) β hβ hβ' = law P Q β hβ hβ' := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (∏ i, (P i).weight (x i) *
      SparseProjection.localDensity β (ratio P Q) i (x i)) =
    ∏ i, (row P Q β hβ hβ' i).weight (x i)
  apply Finset.prod_congr rfl
  intro i _
  rw [row_weight]
  unfold SparseProjection.localDensity
  calc
    _ = (1 - β) * (P i).weight (x i) +
        β * ((P i).weight (x i) * ratio P Q i (x i)) := by ring
    _ = _ := by rw [weight_mul_ratio_of_support P Q support]

theorem forward_eq (P Q : (i : I) → FiniteDistribution (Ω i))
    (support : ∀ i a, (P i).weight a = 0 → (Q i).weight a = 0)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1) :
    ProjectionPosterior.forward P (ratio P Q) (ratio_nonnegative P Q)
      (ratio_mean_one_of_support P Q support) β hβ hβ' =
        markedLaw P Q β hβ hβ'.le := by
  unfold ProjectionPosterior.forward markedLaw
  simp only [ratio_reweight_eq P Q support]

theorem markedLaw_posterior_weight (P Q : (i : I) → FiniteDistribution (Ω i))
    (support : ∀ i a, (P i).weight a = 0 → (Q i).weight a = 0)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (mask : I → Bool) (x : (i : I) → Ω i) :
    (markedLaw P Q β hβ hβ'.le).weight (mask, x) =
      (law P Q β hβ hβ'.le).weight x *
        (ProjectionPosterior.posteriorMask β hβ hβ' (ratio P Q)
          (ratio_nonnegative P Q) x).weight mask := by
  rw [← forward_eq P Q support β hβ hβ']
  rw [ProjectionPosterior.forward_reverse_weight]
  change (SparseProjection.projectedLaw P (ratio P Q) (ratio_nonnegative P Q)
    (ratio_mean_one_of_support P Q support) β hβ hβ'.le).weight x * _ = _
  rw [projectedLaw_eq P Q support β hβ hβ'.le]

theorem observed_variation {Γ : Type*} [Fintype Γ]
    (P Q : (i : I) → FiniteDistribution (Ω i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (B : ℝ) (hB : 0 ≤ B)
    (domination : ∀ i a, (Q i).weight a ≤ B * (P i).weight a)
    (observe : ((i : I) → Ω i) → Γ) :
    ((law P Q β hβ hβ').pushforward observe).totalVariation
        ((FiniteProduct.law P).pushforward observe) ≤
      Real.sqrt ((1 + β ^ 2 * (B - 1)) ^ Fintype.card I - 1) / 2 := by
  rw [← projectedLaw_eq P Q (support_of_domination P Q B domination) β hβ hβ']
  exact SparseProjection.observed_variation P (ratio P Q) (ratio_nonnegative P Q)
    (ratio_mean_one_of_support P Q (support_of_domination P Q B domination))
    β hβ hβ' (B - 1) (ratio_second_moment_le P Q B hB domination) observe

theorem adaptive_selection (P Q : (i : I) → FiniteDistribution (Ω i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1) (B : ℝ) (hB : 0 ≤ B)
    (domination : ∀ i a, (Q i).weight a ≤ B * (P i).weight a)
    (select : ((i : I) → Ω i) → Finset I) (m : Nat)
    (size : ∀ x, (select x).card ≤ m) :
    (markedLaw P Q β hβ hβ'.le).probability
      (fun z => decide (∃ i ∈ select z.2, z.1 i = true)) ≤
        m * (β * B / (1 - β)) := by
  rw [← forward_eq P Q (support_of_domination P Q B domination) β hβ hβ']
  exact AdaptiveProjection.adaptive_selection P (ratio P Q) (ratio_nonnegative P Q)
    (ratio_mean_one_of_support P Q (support_of_domination P Q B domination))
    β hβ hβ' B hB (fun i a => (ratio_bounds_of_domination P Q B hB domination i a).2)
    select m size


variable [Nonempty I] [∀ i, Nonempty (Ω i)]

theorem observed_uniform_variation {Γ : Type*} [Fintype Γ]
    (Q : (i : I) → FiniteDistribution (Ω i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (B : ℝ)
    (cardinality : ∀ i, (Fintype.card (Ω i) : ℝ) ≤ B)
    (observe : ((i : I) → Ω i) → Γ) :
    ((law (fun i => FiniteDistribution.uniform (Ω i)) Q β hβ hβ').pushforward
        observe).totalVariation
      ((FiniteProduct.law (fun i => FiniteDistribution.uniform (Ω i))).pushforward
        observe) ≤
      Real.sqrt ((1 + β ^ 2 * (B - 1)) ^ Fintype.card I - 1) / 2 := by
  have hB : 0 ≤ B := by
    obtain ⟨i⟩ := ‹Nonempty I›
    exact (Nat.cast_nonneg (Fintype.card (Ω i))).trans (cardinality i)
  exact observed_variation (fun i => FiniteDistribution.uniform (Ω i)) Q β hβ hβ'
    B hB (uniform_domination Q B cardinality) observe

theorem adaptive_uniform_selection (Q : (i : I) → FiniteDistribution (Ω i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1) (B : ℝ)
    (cardinality : ∀ i, (Fintype.card (Ω i) : ℝ) ≤ B)
    (select : ((i : I) → Ω i) → Finset I) (m : Nat)
    (size : ∀ x, (select x).card ≤ m) :
    (markedLaw (fun i => FiniteDistribution.uniform (Ω i)) Q β hβ hβ'.le).probability
      (fun z => decide (∃ i ∈ select z.2, z.1 i = true)) ≤
        m * (β * B / (1 - β)) := by
  have hB : 0 ≤ B := by
    obtain ⟨i⟩ := ‹Nonempty I›
    exact (Nat.cast_nonneg (Fintype.card (Ω i))).trans (cardinality i)
  exact adaptive_selection (fun i => FiniteDistribution.uniform (Ω i)) Q β hβ hβ'
    B hB (uniform_domination Q B cardinality) select m size


end
end PerfectCompleteness.SparseReplacement


namespace PerfectCompleteness.MarkedKernelProduct

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

theorem physical_marked {B Y : Type*} {X : B → Type*}
    [Fintype B] [Fintype Y] [∀ b, Fintype (X b)]
    (μ : FiniteDistribution B) (P : (b : B) → FiniteDistribution (X b))
    (f : (b : B) → X b → Y) :
    (μ.mixture (fun b => (P b).pushforward
      (fun x => (⟨b, x⟩ : Σ b, X b)))).pushforward
        (fun x => (x.1, f x.1 x.2)) =
      CleanConditioning.kernelJoint μ (fun b => (P b).pushforward (f b)) := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  rw [FiniteDistribution.probability_pushforward, FiniteDistribution.probability_mixture,
    CleanConditioning.probability_kernelJoint]
  simp only [FiniteDistribution.probability_pushforward]

def markEquiv {I : Type*} {Ω : I → Type*} :
    ((i : I) → Bool × Ω i) ≃ (I → Bool) × ((i : I) → Ω i) where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun x i := (x.1 i, x.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

theorem marked_product (P Q : (i : I) → FiniteDistribution (Ω i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (FiniteProduct.law (fun i => CleanConditioning.kernelJoint
      (ProjectionPosterior.bernoulli β hβ hβ')
      (fun b => if b then Q i else P i))).pushforward (markEquiv (Ω := Ω)) =
      SparseReplacement.markedLaw P Q β hβ hβ' := by
  rw [FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  rintro ⟨mask, x⟩
  change (∏ i, (ProjectionPosterior.bernoulli β hβ hβ').weight (mask i) *
      (if mask i then Q i else P i).weight (x i)) =
    (∏ i, (ProjectionPosterior.bernoulli β hβ hβ').weight (mask i)) *
      ∏ i, (if mask i then Q i else P i).weight (x i)
  rw [Finset.prod_mul_distrib]

variable {Z : I → Type*} [∀ i, Fintype (Z i)]

theorem law_mixture (ρ : (i : I) → FiniteDistribution (Z i))
    (Q : (i : I) → Z i → FiniteDistribution (Ω i)) :
    FiniteProduct.law (fun i => (ρ i).mixture (Q i)) =
      (FiniteProduct.law ρ).mixture
        (fun z => FiniteProduct.law (fun i => Q i (z i))) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (∏ i, (ρ i).expectation (fun z => (Q i z).weight (x i))) =
    (FiniteProduct.law ρ).expectation (fun z => ∏ i, (Q i (z i)).weight (x i))
  exact (FiniteProduct.expectation_product ρ (fun i z => (Q i z).weight (x i))).symm

theorem mixture_markedLaw (P : (i : I) → FiniteDistribution (Ω i))
    (ρ : (i : I) → FiniteDistribution (Z i))
    (Q : (i : I) → Z i → FiniteDistribution (Ω i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (FiniteProduct.law ρ).mixture
        (fun z => SparseReplacement.markedLaw P (fun i => Q i (z i)) β hβ hβ') =
      SparseReplacement.markedLaw P (fun i => (ρ i).mixture (Q i)) β hβ hβ' := by
  apply FiniteDistribution.eq_of_weight_eq
  rintro ⟨mask, x⟩
  let B : ℝ := ∏ i, (ProjectionPosterior.bernoulli β hβ hβ').weight (mask i)
  change (∑ z, (FiniteProduct.law ρ).weight z *
      (B * ∏ i, (if mask i then Q i (z i) else P i).weight (x i))) =
    B * ∏ i, (if mask i then (ρ i).mixture (Q i) else P i).weight (x i)
  calc
    _ = B * (FiniteProduct.law ρ).expectation
        (fun z => ∏ i, (if mask i then Q i (z i) else P i).weight (x i)) := by
      rw [FiniteDistribution.expectation, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      exact mul_left_comm _ _ _
    _ = B * ∏ i, (ρ i).expectation
        (fun z => (if mask i then Q i z else P i).weight (x i)) :=
      congrArg (fun a : ℝ => B * a)
        (FiniteProduct.expectation_product ρ
          (fun i z => (if mask i then Q i z else P i).weight (x i)))
    _ = _ := by
      apply congrArg (fun a : ℝ => B * a)
      apply Finset.prod_congr rfl
      intro i _
      cases mask i with
      | false =>
          exact SmallBias.expectation_const (ρ i) ((P i).weight (x i))
      | true => rfl

end
end PerfectCompleteness.MarkedKernelProduct


namespace PerfectCompleteness.StochasticSingleResponse

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

section FixedFiber

variable {Q A Ω : Type*} [Fintype Q] [DecidableEq Q] [Fintype A] [Fintype Ω]

def hit (responses : Q → FiniteDistribution (Option A)) (ν : FiniteDistribution Ω)
    (ownInput : Ω → Q) (right : A) : ℝ :=
  ν.expectation (fun x => (responses (ownInput x)).probability
    (fun answer => decide (answer = some right)))

def tableHit (ν : FiniteDistribution Ω) (ownInput : Ω → Q) (right : A)
    (answers : Q → Option A) : ℝ :=
  ν.probability (fun x => decide (answers (ownInput x) = some right))

def tableCollision (ν : FiniteDistribution Ω) (ownInput : Ω → Q)
    (answers : Q → Option A) : ℝ :=
  (ν.product ν).probability (TwoResponseCollision.collision (fun x => answers (ownInput x)))

theorem hit_eq_table_mean (responses : Q → FiniteDistribution (Option A))
    (ν : FiniteDistribution Ω) (ownInput : Ω → Q) (right : A) :
    hit responses ν ownInput right =
      (FiniteDistribution.table responses).expectation (tableHit ν ownInput right) := by
  symm
  calc
    _ = (FiniteDistribution.table responses).expectation (fun answers =>
        ν.expectation (fun x => if answers (ownInput x) = some right then 1 else 0)) := by
      apply FiniteDistribution.expectation_congr
      intro answers
      simp only [tableHit, FiniteDistribution.probability, FiniteDistribution.expectation,
        decide_eq_true_eq, mul_ite, mul_one, mul_zero]
    _ = ν.expectation (fun x => (FiniteDistribution.table responses).expectation
        (fun answers => if answers (ownInput x) = some right then 1 else 0)) :=
      FiniteDistribution.expectation_comm (FiniteDistribution.table responses) ν _
    _ = hit responses ν ownInput right := by
      unfold hit
      apply FiniteDistribution.expectation_congr
      intro x
      rw [FiniteDistribution.expectation_table_eval responses (ownInput x)
        (fun answer => if answer = some right then (1 : ℝ) else 0)]
      simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
        decide_eq_true_eq, mul_ite, mul_one, mul_zero]

theorem hit_square_le_table_collision (responses : Q → FiniteDistribution (Option A))
    (ν : FiniteDistribution Ω) (ownInput : Ω → Q) (right : A) :
    hit responses ν ownInput right ^ 2 ≤
      (FiniteDistribution.table responses).expectation (tableCollision ν ownInput) := by
  rw [hit_eq_table_mean]
  apply (CollisionAveraging.mean_square_le (FiniteDistribution.table responses)
    (tableHit ν ownInput right)).trans
  apply Finset.sum_le_sum
  intro answers _
  exact mul_le_mul_of_nonneg_left
    (SingleResponseResampling.local_square_bound ν (fun x => answers (ownInput x)) right)
    ((FiniteDistribution.table responses).nonnegative answers)

theorem hit_square_le_of_supported_tables (responses : Q → FiniteDistribution (Option A))
    (ν : FiniteDistribution Ω) (ownInput : Ω → Q) (right : A) (bound : ℝ)
    (hbound : ∀ answers, (FiniteDistribution.table responses).weight answers ≠ 0 →
      tableCollision ν ownInput answers ≤ bound) :
    hit responses ν ownInput right ^ 2 ≤ bound :=
  (hit_square_le_table_collision responses ν ownInput right).trans
    (DecoderTableAdmissibility.expectation_le_of_support
      (FiniteDistribution.table responses) (tableCollision ν ownInput) bound hbound)

theorem hit_square_le_of_admissible (responses : Q → FiniteDistribution (Option A))
    (ν : FiniteDistribution Ω) (ownInput : Ω → Q) (right : A)
    (valid : Q → A → Prop)
    (hvalid : ∀ q a, (responses q).weight (some a) ≠ 0 → valid q a)
    (bound : ℝ)
    (hbound : ∀ answers, DecoderTableAdmissibility.Admissible valid answers →
      tableCollision ν ownInput answers ≤ bound) :
    hit responses ν ownInput right ^ 2 ≤ bound :=
  (hit_square_le_table_collision responses ν ownInput right).trans
    (DecoderTableAdmissibility.expectation_le_of_admissible responses valid hvalid
      (tableCollision ν ownInput) bound hbound)

theorem hit_square_le_of_probability_one (responses : Q → FiniteDistribution (Option A))
    (ν : FiniteDistribution Ω) (ownInput : Ω → Q) (right : A)
    (valid : Q → A → Prop)
    (hvalid : ∀ q, (responses q).probability
      (fun answer => decide (DecoderTableAdmissibility.RowValid valid q answer)) = 1)
    (bound : ℝ)
    (hbound : ∀ answers, DecoderTableAdmissibility.Admissible valid answers →
      tableCollision ν ownInput answers ≤ bound) :
    hit responses ν ownInput right ^ 2 ≤ bound :=
  (hit_square_le_table_collision responses ν ownInput right).trans
    (DecoderTableAdmissibility.expectation_le_of_probability_one responses valid hvalid
      (tableCollision ν ownInput) bound hbound)

end FixedFiber


variable {B : Type*} [Fintype B]
  {Q A Ω : B → Type*} [∀ b, Fintype (Q b)] [∀ b, DecidableEq (Q b)]
  [∀ b, Fintype (A b)] [∀ b, Fintype (Ω b)]

theorem mean_hit_square_le_table_collision (μ : FiniteDistribution B)
    (responses : (b : B) → Q b → FiniteDistribution (Option (A b)))
    (ν : (b : B) → FiniteDistribution (Ω b))
    (ownInput : (b : B) → Ω b → Q b) (right : (b : B) → A b) :
    μ.expectation (fun b => hit (responses b) (ν b) (ownInput b) (right b)) ^ 2 ≤
      μ.expectation (fun b => (FiniteDistribution.table (responses b)).expectation
        (tableCollision (ν b) (ownInput b))) := by
  apply (CollisionAveraging.mean_square_le μ
    (fun b => hit (responses b) (ν b) (ownInput b) (right b))).trans
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_left
    (hit_square_le_table_collision (responses b) (ν b) (ownInput b) (right b))
    (μ.nonnegative b)

end
end PerfectCompleteness.StochasticSingleResponse

end OAI
