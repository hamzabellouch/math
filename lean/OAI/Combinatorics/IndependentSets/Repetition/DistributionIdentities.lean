import Mathlib
import OAI.Combinatorics.IndependentSets.Repetition.KernelSampling
import OAI.Combinatorics.IndependentSets.Repetition.Mixture
import OAI.Combinatorics.IndependentSets.Repetition.SharedSampling

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition.CompletedSampling

open scoped BigOperators
open Games

noncomputable section

section DistributionIdentities

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

theorem mixture_pushforward_base (μ : FiniteDistribution A) (f : A → B)
    (K : B → FiniteDistribution C) :
    (μ.pushforward f).mixture K = μ.mixture (fun a => K (f a)) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro c
  exact FiniteDistribution.expectation_pushforward μ f (fun b => (K b).weight c)

theorem product_pushforward_eq_mixture_right (μ : FiniteDistribution A)
    (ν : FiniteDistribution B) (f : A × B → C) :
    (μ.product ν).pushforward f =
      ν.mixture (fun b => μ.pushforward (fun a => f (a, b))) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro c
  simp only [FiniteDistribution.pushforward, FiniteDistribution.product,
    FiniteDistribution.mixture, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f (a, b) = c <;> simp [h, mul_comm]

theorem product_product_pushforward_eq_mixture (μ : FiniteDistribution A)
    (ν : FiniteDistribution B) (κ : FiniteDistribution C) (f : A → B → C → D) :
    (μ.product (ν.product κ)).pushforward (fun z => f z.1 z.2.1 z.2.2) =
      (μ.product ν).mixture
        (fun z => κ.pushforward (fun c => f z.1 z.2 c)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro d
  simp only [FiniteDistribution.pushforward, FiniteDistribution.product,
    FiniteDistribution.mixture, Fintype.sum_prod_type]
  simp only [Finset.mul_sum, mul_ite, mul_zero, mul_assoc]

theorem mixture_totalVariation_le (μ ν : FiniteDistribution A)
    (K : A → FiniteDistribution B) :
    (μ.mixture K).totalVariation (ν.mixture K) ≤ μ.totalVariation ν := by
  simpa only [FiniteDistribution.totalVariation, FiniteDistribution.mixture,
    Information.totalVariation, kernelPushforward] using
      totalVariation_kernelPushforward_le μ.weight ν.weight
        (fun a => (K a).weight) (fun a => Information.gameLaw_isProbability (K a))

end DistributionIdentities

section Diagonal

variable {Z S : Type*} [Fintype Z] [Fintype S]

def diagonalLaw (σ : FiniteDistribution (Z × S)) : FiniteDistribution (Z × S × S) :=
  Information.toGameLaw (diagonalWeights σ.weight)
    (diagonalWeights_isProbability _ (Information.gameLaw_isProbability σ))

theorem diagonalLaw_eq_pushforward (σ : FiniteDistribution (Z × S)) :
    diagonalLaw σ = σ.pushforward (fun z => (z.1, z.2, z.2)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  rintro ⟨z, a, b⟩
  change diagonalWeights σ.weight (z, a, b) =
    (σ.pushforward (fun t => (t.1, t.2, t.2))).weight (z, a, b)
  simp only [diagonalWeights, FiniteDistribution.pushforward,
    Fintype.sum_prod_type, Prod.mk.injEq]
  by_cases hab : a = b
  · subst b
    simp [ite_and]
  · simp [hab, ite_and]

theorem diagonalLaw_mixture {T : Type*} [Fintype T]
    (σ : FiniteDistribution (Z × S)) (K : Z × S × S → FiniteDistribution T) :
    (diagonalLaw σ).mixture K = σ.mixture (fun z => K (z.1, z.2, z.2)) := by
  rw [diagonalLaw_eq_pushforward, mixture_pushforward_base]

end Diagonal

variable {X Y S Γ U V : Type*}
  [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ] [Fintype U] [Fintype V]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S]

abbrev Seed (Γ X Y S U V : Type*) :=
  Γ × KernelSampling.Seed (X × S) (Y × S) U V

def seedLaw (γ : FiniteDistribution Γ)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    FiniteDistribution (Seed Γ X Y S U V) :=
  γ.product (KernelSampling.seedLaw L R)

def left (sL : Γ → X → S) (seed : Seed Γ X Y S U V) (x : X) : U :=
  KernelSampling.readLeft seed.2 (x, sL seed.1 x)

def right (sR : Γ → Y → S) (seed : Seed Γ X Y S U V) (y : Y) : V :=
  KernelSampling.readRight seed.2 (y, sR seed.1 y)

def completionKernel (L : X × S → FiniteDistribution U)
    (R : Y × S → FiniteDistribution V) (z : (X × Y) × S × S) :
    FiniteDistribution (U × V) :=
  (L (z.1.1, z.2.1)).product (R (z.1.2, z.2.2))

def outputLaw (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    FiniteDistribution (U × V) :=
  (seedLaw γ L R).mixture (fun seed =>
    μ.pushforward (fun q => (left sL seed q.1, right sR seed q.2)))

theorem outputLaw_eq_product_pushforward
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    outputLaw μ γ sL sR L R =
      (μ.product (seedLaw γ L R)).pushforward
        (fun z => (left sL z.2 z.1.1, right sR z.2 z.1.2)) := by
  exact (product_pushforward_eq_mixture_right μ (seedLaw γ L R)
    (fun z : (X × Y) × Seed Γ X Y S U V =>
      (left sL z.2 z.1.1, right sR z.2 z.1.2))).symm

theorem outputLaw_eq_mixture
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    outputLaw μ γ sL sR L R =
      (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
  calc
    outputLaw μ γ sL sR L R =
        (μ.product γ).mixture (fun z =>
          (KernelSampling.seedLaw L R).pushforward (fun table =>
            (KernelSampling.readLeft table (z.1.1, sL z.2 z.1.1),
             KernelSampling.readRight table (z.1.2, sR z.2 z.1.2)))) := by
      rw [outputLaw_eq_product_pushforward]
      exact product_product_pushforward_eq_mixture μ γ (KernelSampling.seedLaw L R)
        (fun q seed table =>
          (KernelSampling.readLeft table (q.1, sL seed q.1),
           KernelSampling.readRight table (q.2, sR seed q.2)))
    _ = (μ.product γ).mixture (fun z =>
        completionKernel L R (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) := by
      apply congrArg ((μ.product γ).mixture)
      funext z
      exact KernelSampling.read_joint_pushforward L R
        (z.1.1, sL z.2 z.1.1) (z.1.2, sR z.2 z.1.2)
    _ = (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
      exact (mixture_pushforward_base (μ.product γ)
        (fun z => (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) (completionKernel L R)).symm

omit [DecidableEq X] [DecidableEq Y] [DecidableEq S] in

theorem diagonalLaw_completion_mixture
    (σ : FiniteDistribution ((X × Y) × S))
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    (diagonalLaw σ).mixture (completionKernel L R) =
      σ.mixture (fun z => (L (z.1.1, z.2)).product (R (z.1.2, z.2))) := by
  exact diagonalLaw_mixture σ (completionKernel L R)

theorem outputLaw_totalVariation_le
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V)
    (σ : FiniteDistribution ((X × Y) × S)) :
    (outputLaw μ γ sL sR L R).totalVariation
        (σ.mixture (fun z => (L (z.1.1, z.2)).product (R (z.1.2, z.2)))) ≤
      (sharedOutputLaw μ γ sL sR).totalVariation (diagonalLaw σ) := by
  rw [outputLaw_eq_mixture, ← diagonalLaw_completion_mixture σ L R]
  exact mixture_totalVariation_le _ _ (completionKernel L R)

end
end IndependentSetsGames.Foundations.Repetition.CompletedSampling

end OAI
