import OAI.Computability.UniqueGames.Decoding.CoefficientSampling
import OAI.Computability.UniqueGames.Decoding.Experiment

namespace OAI

section

namespace UniqueGamesTheorem.Clean.NativeExperiment

open Foundations.Games
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalGameLaw
open Experiment
open scoped BigOperators

noncomputable section

private theorem expectation_transport {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteDistribution X) (e : X ≃ Y) (f : Y → ℝ) :
    (μ.transport e).expectation f = μ.expectation (fun x => f (e x)) := by
  unfold FiniteDistribution.expectation FiniteDistribution.transport
  exact Fintype.sum_equiv e.symm _ _ (fun _ => by simp)

theorem iid_product_split {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteDistribution X) (ν : FiniteDistribution Y) (k : ℕ) :
    ((μ.product ν).iid k).transport (Game.tupleQuestionEquiv k) =
      (μ.iid k).product (ν.iid k) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro pair
  change (∏ i, μ.weight (pair.1 i) * ν.weight (pair.2 i)) =
    (∏ i, μ.weight (pair.1 i)) * ∏ i, ν.weight (pair.2 i)
  exact Finset.prod_mul_distrib

theorem expectation_iid_product {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteDistribution X) (ν : FiniteDistribution Y) (k : ℕ)
    (f : (Fin k → X × Y) → ℝ) :
    ((μ.product ν).iid k).expectation f =
      (μ.iid k).expectation (fun x =>
        (ν.iid k).expectation (fun y => f (fun i => (x i, y i)))) := by
  have law := expectation_transport ((μ.product ν).iid k)
    (Game.tupleQuestionEquiv k) (fun pair => f (fun i => (pair.1 i, pair.2 i)))
  rw [iid_product_split, FiniteDistribution.expectation_product] at law
  exact law.symm

variable {R O N : Type} [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

def maskSet {k : ℕ} (mask : Fin k → Bool) : Finset (Fin k) :=
  Finset.univ.filter fun i => mask i = true

abbrev MaskStrategy (k : ℕ) (R O N : Type) :=
  (mask : Fin k → Bool) → RawCoefficients (maskSet mask) (Coefficient R) →
    LocalStrategies k R O N

def liftStrategy {k : ℕ} (strategy : MaskStrategy k R O N)
    (extra : Additional k R) (seed : SparseSeed k R) : LocalStrategies k R O N :=
  strategy (fun i => (seed i).1) (coefficients extra seed)

/-- The actual law: independent singleton choices followed by one independent
uniform coefficient at the intercept and each surviving partner coordinate. -/
def success (k : ℕ) (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (strategy : MaskStrategy k R O N) : ℝ :=
  ((bernoulli β hβ₀ hβ₁).iid k).expectation fun mask =>
    (FiniteDistribution.uniform (RawCoefficients (maskSet mask) (Coefficient R))).expectation
      fun gamma => UpperBound.fixedAdviceSuccess μ (maskSet mask) g gamma (strategy mask gamma)

omit [DecidableEq O] [Fintype N] [DecidableEq N] in
theorem success_eq_flat (k : ℕ) (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (strategy : MaskStrategy k R O N) :
    success k μ g β hβ₀ hβ₁ strategy =
      Experiment.success k μ g (FiniteDistribution.uniform (Additional k R))
        β hβ₀ hβ₁ (liftStrategy strategy) := by
  unfold success Experiment.success singletonSlopeLaw
  symm
  calc
    _ = (FiniteDistribution.uniform (Additional k R)).expectation fun extra =>
        ((bernoulli β hβ₀ hβ₁).iid k).expectation fun mask =>
          (FiniteDistribution.uniform (Fin k → Coefficient R)).expectation fun single =>
            UpperBound.fixedAdviceSuccess μ (maskSet mask) g
              (CoefficientSampling.selectCoefficients (maskSet mask) extra single)
              (strategy mask (CoefficientSampling.selectCoefficients (maskSet mask) extra single)) := by
      apply FiniteDistribution.expectation_congr
      intro extra
      rw [expectation_iid_product, FiniteDistribution.iid_uniform]
      apply FiniteDistribution.expectation_congr
      intro mask
      apply FiniteDistribution.expectation_congr
      intro single
      have hgamma : coefficients extra (fun i => (mask i, single i)) =
          CoefficientSampling.selectCoefficients (maskSet mask) extra single := by
        funext slot
        cases slot with
        | none => rfl
        | some slot =>
          cases slot with
          | inl pair => rfl
          | inr i => rfl
      change UpperBound.fixedAdviceSuccess μ (maskSet mask) g
        (coefficients extra (fun i => (mask i, single i)))
        (strategy mask (coefficients extra (fun i => (mask i, single i)))) = _
      rw [hgamma]
    _ = ((bernoulli β hβ₀ hβ₁).iid k).expectation (fun mask =>
        (FiniteDistribution.uniform (Additional k R)).expectation fun extra =>
          (FiniteDistribution.uniform (Fin k → Coefficient R)).expectation fun single =>
            UpperBound.fixedAdviceSuccess μ (maskSet mask) g
              (CoefficientSampling.selectCoefficients (maskSet mask) extra single)
              (strategy mask (CoefficientSampling.selectCoefficients (maskSet mask) extra single))) :=
      FiniteDistribution.expectation_comm _ _ _
    _ = _ := by
      apply FiniteDistribution.expectation_congr
      intro mask
      exact CoefficientSampling.uniform_selectCoefficients (maskSet mask)
        (fun gamma => UpperBound.fixedAdviceSuccess μ (maskSet mask) g gamma (strategy mask gamma))

end
end UniqueGamesTheorem.Clean.NativeExperiment

end

end OAI
