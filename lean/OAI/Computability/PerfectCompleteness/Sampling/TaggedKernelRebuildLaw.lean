import OAI.Computability.PerfectCompleteness.Foundations.DependentPredictionDifferenceLemmas
import OAI.Computability.PerfectCompleteness.Repetition.CleanConditioning
import OAI.Computability.UniqueGames.Foundations.ValueLemmas

namespace OAI

section

namespace PerfectCompleteness.TaggedKernelRebuildLaw

open UniqueGamesTheorem.Foundations.Games CompletionSoundness

noncomputable section

private theorem probability_eq_expectation {X : Type*} [Fintype X]
    (μ : FiniteDistribution X) (event : X → Bool) :
    μ.probability event = μ.expectation (fun x => if event x then 1 else 0) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    mul_ite, mul_one, mul_zero]

private theorem expectation_sigmaLaw {B : Type*} [Fintype B]
    {V : B → Type*} [∀ b, Fintype (V b)]
    (β : FiniteDistribution B) (ν : (b : B) → FiniteDistribution (V b))
    (f : (Σ b, V b) → ℝ) :
    (sigmaLaw β ν).expectation f =
      β.expectation (fun b => (ν b).expectation (fun v => f ⟨b, v⟩)) := by
  simp only [FiniteDistribution.expectation, sigmaLaw,
    Fintype.sum_sigma, Finset.mul_sum, mul_assoc]

private theorem expectation_kernelJoint {S R : Type*} [Fintype S] [Fintype R]
    (μ : FiniteDistribution S) (P : S → FiniteDistribution R) (f : S × R → ℝ) :
    (CleanConditioning.kernelJoint μ P).expectation f =
      μ.expectation (fun s => (P s).expectation (fun r => f (s, r))) := by
  simp only [FiniteDistribution.expectation, CleanConditioning.kernelJoint,
    Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

private theorem expectation_rebuild {R E B : Type*}
    [Fintype R] [Fintype E] [Fintype B]
    {V Y : B → Type*} [∀ b, Fintype (V b)] [∀ b, Fintype (Y b)]
    (β : FiniteDistribution B) (δ : FiniteDistribution E) (P : FiniteDistribution R)
    (ν : (b : B) → FiniteDistribution (V b))
    (Q : (b : B) → FiniteDistribution (Y b))
    (decode : R → Σ b, V b) (rebuild : (b : B) → E → V b → Y b)
    (hdecode : P.pushforward decode = sigmaLaw β ν)
    (hbuild : ∀ b, (δ.product (ν b)).pushforward
      (fun x => rebuild b x.1 x.2) = Q b)
    (f : (Σ b, Y b) → ℝ) :
    (δ.product P).expectation
        (fun x => f ⟨(decode x.2).1, rebuild _ x.1 (decode x.2).2⟩) =
      (sigmaLaw β Q).expectation f := by
  calc
    _ = δ.expectation (fun e => (P.pushforward decode).expectation
        (fun bv => f ⟨bv.1, rebuild bv.1 e bv.2⟩)) := by
      rw [FiniteDistribution.expectation_product]
      apply FiniteDistribution.expectation_congr
      intro e
      exact (FiniteDistribution.expectation_pushforward P decode
        (fun bv => f ⟨bv.1, rebuild bv.1 e bv.2⟩)).symm
    _ = δ.expectation (fun e => β.expectation
        (fun b => (ν b).expectation (fun v => f ⟨b, rebuild b e v⟩))) := by
      simp only [hdecode, expectation_sigmaLaw]
    _ = β.expectation (fun b => δ.expectation
        (fun e => (ν b).expectation (fun v => f ⟨b, rebuild b e v⟩))) :=
      FiniteDistribution.expectation_comm δ β _
    _ = β.expectation (fun b => (Q b).expectation (fun y => f ⟨b, y⟩)) := by
      apply FiniteDistribution.expectation_congr
      intro b
      calc
        _ = (δ.product (ν b)).expectation
            (fun x => f ⟨b, rebuild b x.1 x.2⟩) :=
          (FiniteDistribution.expectation_product δ (ν b) _).symm
        _ = ((δ.product (ν b)).pushforward
            (fun x => rebuild b x.1 x.2)).expectation (fun y => f ⟨b, y⟩) :=
          (FiniteDistribution.expectation_pushforward
            (δ.product (ν b)) (fun x => rebuild b x.1 x.2)
            (fun y => f ⟨b, y⟩)).symm
        _ = _ := by rw [hbuild b]
    _ = _ := (expectation_sigmaLaw β Q f).symm

theorem fiber_rebuild_law {R E B : Type*}
    [Fintype R] [Fintype E] [Fintype B]
    {V Y : B → Type*} [∀ b, Fintype (V b)] [∀ b, Fintype (Y b)]
    (β : FiniteDistribution B) (δ : FiniteDistribution E) (P : FiniteDistribution R)
    (ν : (b : B) → FiniteDistribution (V b))
    (Q : (b : B) → FiniteDistribution (Y b))
    (decode : R → Σ b, V b) (rebuild : (b : B) → E → V b → Y b)
    (hdecode : P.pushforward decode = sigmaLaw β ν)
    (hbuild : ∀ b, (δ.product (ν b)).pushforward
      (fun x => rebuild b x.1 x.2) = Q b) :
    (δ.product P).pushforward
        (fun x => (⟨(decode x.2).1, rebuild _ x.1 (decode x.2).2⟩ : Σ b, Y b)) =
      sigmaLaw β Q := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  simp only [probability_eq_expectation, FiniteDistribution.expectation_pushforward]
  exact expectation_rebuild β δ P ν Q decode rebuild hdecode hbuild
    (fun x => if event x then 1 else 0)

theorem rebuild_law {S R E B : Type*}
    [Fintype S] [Fintype R] [Fintype E] [Fintype B]
    {V Y : S → B → Type*}
    [∀ s b, Fintype (V s b)] [∀ s b, Fintype (Y s b)]
    (μ : FiniteDistribution S) (β : FiniteDistribution B) (δ : FiniteDistribution E)
    (P : S → FiniteDistribution R)
    (ν : (s : S) → (b : B) → FiniteDistribution (V s b))
    (Q : (s : S) → (b : B) → FiniteDistribution (Y s b))
    (decode : (s : S) → R → Σ b, V s b)
    (rebuild : (s : S) → (b : B) → E → V s b → Y s b)
    (hdecode : ∀ s, (P s).pushforward (decode s) = sigmaLaw β (ν s))
    (hbuild : ∀ s b, (δ.product (ν s b)).pushforward
      (fun x => rebuild s b x.1 x.2) = Q s b) :
    ((CleanConditioning.kernelJoint μ P).product δ).pushforward
        (fun x => (⟨(x.1.1, (decode x.1.1 x.1.2).1),
          rebuild x.1.1 _ x.2 (decode x.1.1 x.1.2).2⟩ :
            Σ sb : S × B, Y sb.1 sb.2)) =
      sigmaLaw (μ.product β) (fun sb => Q sb.1 sb.2) := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  simp only [probability_eq_expectation, FiniteDistribution.expectation_pushforward,
    FiniteDistribution.expectation_product, expectation_kernelJoint, expectation_sigmaLaw]
  apply FiniteDistribution.expectation_congr
  intro s
  have h := expectation_rebuild β δ (P s) (ν s) (Q s) (decode s) (rebuild s)
    (hdecode s) (hbuild s)
    (fun bv => if event ⟨(s, bv.1), bv.2⟩ then 1 else 0)
  rw [FiniteDistribution.expectation_product, expectation_sigmaLaw] at h
  exact (FiniteDistribution.expectation_comm (P s) δ _).trans h

end
end PerfectCompleteness.TaggedKernelRebuildLaw

end

end OAI
