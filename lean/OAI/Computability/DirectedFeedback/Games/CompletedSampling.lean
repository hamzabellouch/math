import Mathlib
import OAI.Computability.DirectedFeedback.Games.Game
import OAI.Computability.DirectedFeedback.Games.SelectedLikelihood

namespace OAI

namespace DFVSGames.Foundations.Repetition.CompletedSampling

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

section Completion

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

end Completion

variable {I X Y S Γ : Type*}
  [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y] [DecidableEq S]

def coordinateLeft (j : I) (sL : Γ → X → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (x : X) : I → X :=
  KernelSampling.completedLeft j seed.2 (x, sL seed.1 x)

def coordinateRight (j : I) (sR : Γ → Y → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (y : Y) : I → Y :=
  KernelSampling.completedRight j seed.2 (y, sR seed.1 y)

omit [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S] in
@[simp] theorem coordinateLeft_preserves (j : I) (sL : Γ → X → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (x : X) :
    coordinateLeft j sL seed x j = x := by
  simp [coordinateLeft]

omit [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S] in
@[simp] theorem coordinateRight_preserves (j : I) (sR : Γ → Y → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (y : Y) :
    coordinateRight j sR seed y j = y := by
  simp [coordinateRight]

def coordinateOutputLaw (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y)) :
    FiniteDistribution ((I → X) × (I → Y)) :=
  (seedLaw γ L R).mixture (fun seed => μ.pushforward
    (fun q => (coordinateLeft j sL seed q.1, coordinateRight j sR seed q.2)))

theorem coordinateOutputLaw_eq_mixture
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y))
    (hL : ∀ q xs, (L q).weight xs ≠ 0 → xs j = q.1)
    (hR : ∀ q ys, (R q).weight ys ≠ 0 → ys j = q.1) :
    coordinateOutputLaw μ γ j sL sR L R =
      (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
  calc
    coordinateOutputLaw μ γ j sL sR L R =
        (μ.product (seedLaw γ L R)).pushforward
          (fun z => (coordinateLeft j sL z.2 z.1.1,
            coordinateRight j sR z.2 z.1.2)) := by
      exact (product_pushforward_eq_mixture_right μ (seedLaw γ L R)
        (fun z : (X × Y) × Seed Γ X Y S (I → X) (I → Y) =>
          (coordinateLeft j sL z.2 z.1.1, coordinateRight j sR z.2 z.1.2))).symm
    _ = (μ.product γ).mixture (fun z =>
        (KernelSampling.seedLaw L R).pushforward (fun table =>
          (KernelSampling.completedLeft j table (z.1.1, sL z.2 z.1.1),
           KernelSampling.completedRight j table (z.1.2, sR z.2 z.1.2)))) := by
      exact product_product_pushforward_eq_mixture μ γ (KernelSampling.seedLaw L R)
        (fun q seed table =>
          (KernelSampling.completedLeft j table (q.1, sL seed q.1),
           KernelSampling.completedRight j table (q.2, sR seed q.2)))
    _ = (μ.product γ).mixture (fun z =>
        completionKernel L R (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) := by
      apply congrArg ((μ.product γ).mixture)
      funext z
      exact KernelSampling.completed_joint_pushforward L R j hL hR
        (z.1.1, sL z.2 z.1.1) (z.1.2, sR z.2 z.1.2)
    _ = (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
      exact (mixture_pushforward_base (μ.product γ)
        (fun z => (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) (completionKernel L R)).symm

theorem coordinateOutputLaw_eq_outputLaw
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y))
    (hL : ∀ q xs, (L q).weight xs ≠ 0 → xs j = q.1)
    (hR : ∀ q ys, (R q).weight ys ≠ 0 → ys j = q.1) :
    coordinateOutputLaw μ γ j sL sR L R = outputLaw μ γ sL sR L R := by
  rw [coordinateOutputLaw_eq_mixture μ γ j sL sR L R hL hR, outputLaw_eq_mixture]

theorem coordinateOutputLaw_totalVariation_le
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y))
    (hL : ∀ q xs, (L q).weight xs ≠ 0 → xs j = q.1)
    (hR : ∀ q ys, (R q).weight ys ≠ 0 → ys j = q.1)
    (σ : FiniteDistribution ((X × Y) × S)) :
    (coordinateOutputLaw μ γ j sL sR L R).totalVariation
        (σ.mixture (fun z => (L (z.1.1, z.2)).product (R (z.1.2, z.2)))) ≤
      (sharedOutputLaw μ γ sL sR).totalVariation (diagonalLaw σ) := by
  rw [coordinateOutputLaw_eq_outputLaw μ γ j sL sR L R hL hR]
  exact outputLaw_totalVariation_le μ γ sL sR L R σ

end

end DFVSGames.Foundations.Repetition.CompletedSampling

namespace DFVSGames.Foundations.Games.Game

noncomputable section

variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ Seed : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂] [Fintype Seed]
  [Nonempty A₁] [Nonempty A₂]

def localEmbeddingLaw (G : Game Q₁ Q₂ A₁ A₂)
    (seedLaw : FiniteDistribution Seed)
    (left : Seed → Q₁ → R₁) (right : Seed → Q₂ → R₂) :
    FiniteDistribution (R₁ × R₂) :=
  seedLaw.mixture fun seed =>
    G.questions.pushforward fun q => (left seed q.1, right seed q.2)

theorem success_le_value_add_embedding_distance
    (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂)
    (seedLaw : FiniteDistribution Seed)
    (left : Seed → Q₁ → R₁) (right : Seed → Q₂ → R₂)
    (answerLeft : Seed → Q₁ → B₁ → A₁)
    (answerRight : Seed → Q₂ → B₂ → A₂)
    (acceptance : ∀ seed x y a b,
      H.accepts (left seed x) (right seed y) a b = true →
      G.accepts x y (answerLeft seed x a) (answerRight seed y b) = true)
    (strategy : Strategy R₁ R₂ B₁ B₂) :
    H.success strategy ≤ G.value +
      H.questions.totalVariation (G.localEmbeddingLaw seedLaw left right) := by
  have localBound (seed : Seed) :
      (G.questions.pushforward (fun q => (left seed q.1, right seed q.2))).probability
        (H.wins strategy) ≤ G.value := by
    let embedded : Game R₁ R₂ B₁ B₂ :=
      { questions := G.questions.pushforward fun q => (left seed q.1, right seed q.2)
        accepts := H.accepts }
    change embedded.success strategy ≤ G.value
    exact (G.success_le_of_localSimulation embedded (left seed) (right seed)
      (answerLeft seed) (answerRight seed) rfl (acceptance seed) strategy).trans
      (G.success_le_value _)
  have mixtureBound :
      (G.localEmbeddingLaw seedLaw left right).probability (H.wins strategy) ≤ G.value :=
    seedLaw.probability_mixture_le _ _ _ localBound
  exact (H.questions.probability_le_add_totalVariation
    (G.localEmbeddingLaw seedLaw left right) (H.wins strategy)).trans
    (add_le_add mixtureBound (le_refl _))

def coordinateGame (G : Game Q₁ Q₂ A₁ A₂) {n : Nat} (coordinate : Fin n)
    (law : FiniteDistribution ((Fin n → Q₁) × (Fin n → Q₂))) :
    Game (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂) where
  questions := law
  accepts x y a b := G.accepts (x coordinate) (y coordinate) (a coordinate) (b coordinate)

theorem coordinate_probability_le_value_add_embedding_distance
    (G : Game Q₁ Q₂ A₁ A₂) {n : Nat} (coordinate : Fin n)
    (law : FiniteDistribution ((Fin n → Q₁) × (Fin n → Q₂)))
    (seedLaw : FiniteDistribution Seed)
    (left : Seed → Q₁ → Fin n → Q₁) (right : Seed → Q₂ → Fin n → Q₂)
    (left_preserves : ∀ seed x, left seed x coordinate = x)
    (right_preserves : ∀ seed y, right seed y coordinate = y)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    law.probability (G.coordinateWin strategy coordinate) ≤ G.value +
      law.totalVariation (G.localEmbeddingLaw seedLaw left right) := by
  apply G.success_le_value_add_embedding_distance (G.coordinateGame coordinate law)
    seedLaw left right (fun _ _ a => a coordinate) (fun _ _ b => b coordinate)
  intro seed x y a b h
  simpa only [coordinateGame, left_preserves, right_preserves] using h

theorem coordinate_probability_le_value_of_approximate_embeddings
    {SeedFamily : Nat → Type*} [∀ t, Fintype (SeedFamily t)]
    (G : Game Q₁ Q₂ A₁ A₂) {n : Nat} (coordinate : Fin n)
    (law : FiniteDistribution ((Fin n → Q₁) × (Fin n → Q₂)))
    (seedLaw : (t : Nat) → FiniteDistribution (SeedFamily t))
    (left : (t : Nat) → SeedFamily t → Q₁ → Fin n → Q₁)
    (right : (t : Nat) → SeedFamily t → Q₂ → Fin n → Q₂)
    (left_preserves : ∀ t seed x, left t seed x coordinate = x)
    (right_preserves : ∀ t seed y, right t seed y coordinate = y)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (distance : ℝ)
    (close : ∀ η : ℝ, 0 < η → ∃ t,
      law.totalVariation (G.localEmbeddingLaw (seedLaw t) (left t) (right t)) ≤
        distance + η) :
    law.probability (G.coordinateWin strategy coordinate) ≤ G.value + distance := by
  by_contra h
  have gap : 0 < law.probability (G.coordinateWin strategy coordinate) -
      (G.value + distance) := sub_pos.mpr (lt_of_not_ge h)
  obtain ⟨t, ht⟩ := close
    ((law.probability (G.coordinateWin strategy coordinate) - (G.value + distance)) / 2)
    (by linarith)
  have bound := G.coordinate_probability_le_value_add_embedding_distance coordinate law
    (seedLaw t) (left t) (right t) (left_preserves t) (right_preserves t) strategy
  linarith

end
end DFVSGames.Foundations.Games.Game

namespace DFVSGames.Foundations.Repetition
open scoped BigOperators
open Games CorrelatedSampling
noncomputable section
variable {Q₁ Q₂ A₁ A₂ S : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype S]
  [Nonempty A₁] [Nonempty A₂] [Nonempty S]
  [DecidableEq Q₁] [DecidableEq Q₂] [DecidableEq S] {n : Nat}

theorem coordinate_probability_le_value_of_local_completion
    (G : Game Q₁ Q₂ A₁ A₂) (j : Fin n)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (σ : FiniteDistribution ((Q₁ × Q₂) × S))
    (profileL : Q₁ → FiniteDistribution S) (profileR : Q₂ → FiniteDistribution S)
    (completionL : Q₁ × S → FiniteDistribution (Fin n → Q₁))
    (completionR : Q₂ × S → FiniteDistribution (Fin n → Q₂))
    (supportL : ∀ q xs, (completionL q).weight xs ≠ 0 → xs j = q.1)
    (supportR : ∀ q ys, (completionR q).weight ys ≠ 0 → ys j = q.1)
    (fallback : S) :
    (σ.mixture (fun z => (completionL (z.1.1,z.2)).product
      (completionR (z.1.2,z.2)))).probability (G.coordinateWin strategy j) ≤
      G.value +
        (2 * Information.totalVariation σ.weight
          (fun z => G.questions.weight z.1 * (profileL z.1.1).weight z.2) +
         2 * Information.totalVariation σ.weight
          (fun z => G.questions.weight z.1 * (profileR z.1.2).weight z.2)) := by
  let targetLaw := σ.mixture (fun z => (completionL (z.1.1,z.2)).product (completionR (z.1.2,z.2)))
  let δ := 2 * Information.totalVariation σ.weight
      (fun z => G.questions.weight z.1 * (profileL z.1.1).weight z.2) +
    2 * Information.totalVariation σ.weight
      (fun z => G.questions.weight z.1 * (profileR z.1.2).weight z.2)
  change targetLaw.probability (G.coordinateWin strategy j) ≤ G.value + δ
  by_contra h
  have gap : 0 < targetLaw.probability (G.coordinateWin strategy j) - (G.value + δ) :=
    sub_pos.mpr (lt_of_not_ge h)
  let η := (targetLaw.probability (G.coordinateWin strategy j) - (G.value + δ)) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨N,hN⟩ := samplerOutputLaw_arbitrarily_close σ G.questions profileL profileR fallback η hη
  let thresholds := sharedProfileThresholds profileL profileR
  let γ := traceSeedLaw (rectangleDistribution (α := S) thresholds) N
  let sL := samplerLocal thresholds profileL fallback N
  let sR := samplerLocal thresholds profileR fallback N
  have hvariation := CompletedSampling.coordinateOutputLaw_totalVariation_le
    G.questions γ j sL sR completionL completionR supportL supportR σ
  have hclose : (CompletedSampling.coordinateOutputLaw G.questions γ j sL sR completionL completionR).totalVariation targetLaw ≤ δ + η :=
    hvariation.trans hN
  have hsuccess := G.coordinate_probability_le_value_add_embedding_distance j targetLaw
    (CompletedSampling.seedLaw γ completionL completionR)
    (CompletedSampling.coordinateLeft j sL) (CompletedSampling.coordinateRight j sR)
    (CompletedSampling.coordinateLeft_preserves j sL)
    (CompletedSampling.coordinateRight_preserves j sR) strategy
  have hsym : targetLaw.totalVariation
      (G.localEmbeddingLaw (CompletedSampling.seedLaw γ completionL completionR)
        (CompletedSampling.coordinateLeft j sL) (CompletedSampling.coordinateRight j sR)) =
      (CompletedSampling.coordinateOutputLaw G.questions γ j sL sR completionL completionR).totalVariation targetLaw := by
    unfold FiniteDistribution.totalVariation
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    exact abs_sub_comm _ _
  rw [hsym] at hsuccess
  dsimp [η] at hclose
  linarith

end
end DFVSGames.Foundations.Repetition

namespace DFVSGames.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : ℕ}

theorem selectedLabels_card (selected : Finset (Fin n)) :
    Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) =
      (Fintype.card A₁ * Fintype.card A₂) ^ selected.card := by
  simp [SelectedLabels, Fintype.card_prod, mul_pow]

theorem unusedCoordinates_card (selected : Finset (Fin n)) :
    Fintype.card {i : Fin n // i ∉ selected} = n - selected.card := by
  classical
  simp

theorem unusedCoordinates_card_real (selected : Finset (Fin n)) :
    (Fintype.card {i : Fin n // i ∉ selected} : ℝ) = (n : ℝ) - selected.card := by
  have hs : selected.card ≤ n := by simpa using Finset.card_le_univ selected
  rw [unusedCoordinates_card, Nat.cast_sub hs]

theorem log_le_logTwo {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ logTwo x := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwo_le : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1 ; norm_num
  unfold logTwo
  apply (le_div_iff₀ htwo).2
  simpa using mul_le_mul_of_nonneg_left htwo_le hlog

theorem selectedLabels_log_le [Nonempty A₁] [Nonempty A₂]
    (selected : Finset (Fin n)) (ell : ℝ)
    (hell : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    Real.log (Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ) ≤
      (selected.card : ℝ) * ell := by
  have ha : (1 : ℝ) ≤ Fintype.card A₁ := by exact_mod_cast Fintype.card_pos (α := A₁)
  have hb : (1 : ℝ) ≤ Fintype.card A₂ := by exact_mod_cast Fintype.card_pos (α := A₂)
  have hab : (1 : ℝ) ≤ (Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ) := by nlinarith
  rw [selectedLabels_card, Nat.cast_pow, Nat.cast_mul, Real.log_pow]
  exact mul_le_mul_of_nonneg_left ((log_le_logTwo hab).trans hell) (Nat.cast_nonneg _)

omit [DecidableEq Q₁] [DecidableEq Q₂] in

theorem selectedInformationRadius_le [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (ell : ℝ)
    (hell : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    selectedInformationRadius G strategy selected ≤
      Real.sqrt (((n : ℝ) - selected.card) *
        ((selected.card : ℝ) * ell + logTwo (1 / G.selectedSuccess strategy selected))) := by
  have hprob : 1 ≤ 1 / G.selectedSuccess strategy selected := by
    apply (le_div_iff₀ positive).2
    simpa using G.selectedSuccess_le_one strategy selected
  have hbudget := add_le_add (selectedLabels_log_le (A₁ := A₁) (A₂ := A₂) selected ell hell)
    (log_le_logTwo hprob)
  unfold selectedInformationRadius
  rw [← unusedCoordinates_card_real selected]
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg _)

theorem sqrt_budget_factor (a b : ℝ) (ha : 0 < a) :
    Real.sqrt (a * b) = a * Real.sqrt (b / a) := by
  have he : a * b = a ^ 2 * (b / a) := by
    field_simp
  rw [he, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq (le_of_lt ha)]

omit [DecidableEq Q₁] [DecidableEq Q₂] in

theorem exists_coordinate_le_information_budget [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (ell : ℝ)
    (hell : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell)
    (hselected : selected.card < n)
    (error : {i : Fin n // i ∉ selected} → ℝ)
    (hsum : (∑ j, error j) ≤ 15 * selectedInformationRadius G strategy selected) :
    ∃ j : {i : Fin n // i ∉ selected}, error j ≤ 15 * Real.sqrt
      (((selected.card : ℝ) * ell + logTwo (1 / G.selectedSuccess strategy selected)) /
        ((n : ℝ) - selected.card)) := by
  classical
  have hcard : 0 < Fintype.card {i : Fin n // i ∉ selected} := by
    rw [unusedCoordinates_card]
    exact Nat.sub_pos_of_lt hselected
  let : Nonempty {i : Fin n // i ∉ selected} := Fintype.card_pos_iff.mp hcard
  have hden : 0 < (n : ℝ) - selected.card := by
    rw [← unusedCoordinates_card_real selected]
    exact_mod_cast hcard
  have htotal := hsum.trans (mul_le_mul_of_nonneg_left
    (selectedInformationRadius_le G strategy selected positive ell hell) (by norm_num : (0 : ℝ) ≤ 15))
  rw [sqrt_budget_factor _ _ hden] at htotal
  have havg : (∑ j, error j) ≤ ∑ _j : {i : Fin n // i ∉ selected},
      15 * Real.sqrt
        (((selected.card : ℝ) * ell + logTwo (1 / G.selectedSuccess strategy selected)) /
          ((n : ℝ) - selected.card)) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      unusedCoordinates_card_real, mul_assoc, mul_left_comm] using htotal
  obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty havg
  exact ⟨j, hj⟩

end
end DFVSGames.Foundations.Repetition

namespace DFVSGames.Foundations.Repetition.SelectionSequence

private theorem exists_unused_inline_SelectionSequence {n : Nat} (S : Finset (Fin n)) (hcard : S.card < n) :
    ∃ j : Fin n, j ∉ S := by
  classical
  apply Classical.byContradiction
  intro h
  have hall : ∀ j : Fin n, j ∈ S := by
    intro j
    apply Classical.byContradiction
    intro hj
    exact h ⟨j, hj⟩
  have hfull : S = Finset.univ :=
    Finset.ext (fun j => iff_of_true (hall j) (Finset.mem_univ j))
  have hbad : n < n := by
    simpa only [hfull, Finset.card_univ, Fintype.card_fin] using hcard
  exact Nat.lt_irrefl n hbad

noncomputable def nextSet {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j)
    (S : Finset (Fin n)) : Finset (Fin n) :=
  if hs : S.card < n then insert (Classical.choose (witness S hs)) S else S

noncomputable def selectedSet {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j) : Nat → Finset (Fin n)
  | 0 => ∅
  | m + 1 => nextSet Step witness (selectedSet Step witness m)

theorem selectedSet_card {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j) (m : Nat) :
    (selectedSet Step witness m).card = min m n := by
  induction m with
  | zero => simp [selectedSet]
  | succ m ih =>
    by_cases hm : m < n
    · have hc : (selectedSet Step witness m).card = m := by
        simpa only [Nat.min_eq_left (Nat.le_of_lt hm)] using ih
      have hs : (selectedSet Step witness m).card < n := by
        simpa only [hc] using hm
      rw [selectedSet, nextSet, dite_eq_left hs,
        Finset.card_insert_of_notMem ((Classical.choose_spec (witness _ hs)).1),
        hc, Nat.min_eq_left (Nat.succ_le_of_lt hm)]
    · have hc : (selectedSet Step witness m).card = n := by
        simpa only [Nat.min_eq_right (Nat.le_of_not_gt hm)] using ih
      have hs : ¬(selectedSet Step witness m).card < n := by
        rw [hc]
        exact Nat.not_lt.mpr (Nat.le_refl n)
      rw [selectedSet, nextSet, dite_eq_right hs, hc,
        Nat.min_eq_right (Nat.le_trans (Nat.le_of_not_gt hm) (Nat.le_succ m))]

theorem selectedSet_subset_succ {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j) (m : Nat) :
    selectedSet Step witness m ⊆ selectedSet Step witness (m + 1) := by
  change selectedSet Step witness m ⊆ nextSet Step witness (selectedSet Step witness m)
  unfold nextSet
  split
  · exact Finset.subset_insert _ _
  · exact le_rfl

theorem selectedSet_monotone {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j) :
    Monotone (selectedSet Step witness) :=
  monotone_nat_of_le_succ (selectedSet_subset_succ Step witness)

theorem selectedSet_univ {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j) :
    selectedSet Step witness n = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simp [selectedSet_card]

theorem selectedSet_step {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j)
    (m : Nat) (hm : m < n) :
    ∃ j, j ∉ selectedSet Step witness m ∧
      selectedSet Step witness (m + 1) = insert j (selectedSet Step witness m) ∧
      Step (selectedSet Step witness m) j := by
  have hc : (selectedSet Step witness m).card = m := by
    rw [selectedSet_card, Nat.min_eq_left (Nat.le_of_lt hm)]
  have hs : (selectedSet Step witness m).card < n := by simpa only [hc] using hm
  let j := Classical.choose (witness (selectedSet Step witness m) hs)
  have hj := Classical.choose_spec (witness (selectedSet Step witness m) hs)
  refine ⟨j, hj.1, ?_, hj.2⟩
  simp only [selectedSet, nextSet, dite_eq_left hs, j]

def SetStep {n : Nat} (P : Finset (Fin n) → ℝ) (v ell : ℝ)
    (S : Finset (Fin n)) (j : Fin n) : Prop :=
  P (insert j S) ≤ P S *
    (v + 15 * Real.sqrt (((S.card : ℝ) * ell + logTwo (1 / P S)) /
      ((n : ℝ) - S.card)))

theorem totalSetStep {n : Nat} (P : Finset (Fin n) → ℝ) (v ell : ℝ)
    (hnonneg : ∀ S, 0 ≤ P S) (hanti : Antitone P)
    (hpositive : ∀ S, S.card < n → 0 < P S →
      ∃ j, j ∉ S ∧ SetStep P v ell S j) :
    ∀ S, S.card < n → ∃ j, j ∉ S ∧ SetStep P v ell S j := by
  intro S hcard
  by_cases hp : 0 < P S
  · exact hpositive S hcard hp
  · obtain ⟨j, hj⟩ := exists_unused_inline_SelectionSequence S hcard
    have hz : P S = 0 := le_antisymm (le_of_not_gt hp) (hnonneg S)
    have hnext : P (insert j S) = 0 := le_antisymm
      ((hanti (Finset.subset_insert j S)).trans (le_of_eq hz)) (hnonneg (insert j S))
    refine ⟨j, hj, ?_⟩
    simpa only [SetStep, hnext, hz, zero_mul] using (le_refl (0 : ℝ))

theorem exists_scalar_sequence {n : Nat} (P : Finset (Fin n) → ℝ) (v ell : ℝ)
    (hempty : P ∅ = 1) (hnonneg : ∀ S, 0 ≤ P S) (hanti : Antitone P)
    (hpositive : ∀ S, S.card < n → 0 < P S →
      ∃ j, j ∉ S ∧ SetStep P v ell S j) :
    ∃ p : Nat → ℝ, p 0 = 1 ∧ (∀ m, 0 ≤ p m) ∧ Antitone p ∧
      ScalarRecurrence p n v ell ∧ p n = P Finset.univ := by
  let witness := totalSetStep P v ell hnonneg hanti hpositive
  let sets := selectedSet (SetStep P v ell) witness
  let p := fun m => P (sets m)
  refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩
  · change P (selectedSet (SetStep P v ell) witness 0) = 1
    simpa only [selectedSet] using hempty
  · intro m
    exact hnonneg (sets m)
  · intro i j hij
    exact hanti (selectedSet_monotone (SetStep P v ell) witness hij)
  · intro m hm
    obtain ⟨j, _, hnext, hbound⟩ :=
      selectedSet_step (SetStep P v ell) witness m hm
    have hc : (selectedSet (SetStep P v ell) witness m).card = m := by
      rw [selectedSet_card, Nat.min_eq_left (Nat.le_of_lt hm)]
    change P (selectedSet (SetStep P v ell) witness (m + 1)) ≤ _
    rw [hnext]
    simpa only [SetStep, hc] using hbound
  · change P (selectedSet (SetStep P v ell) witness n) = P Finset.univ
    rw [selectedSet_univ]

open DFVSGames.Foundations.Games

variable {Q₁ Q₂ A₁ A₂ : Type*}
variable [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
variable [Nonempty A₁] [Nonempty A₂]

def ConditionalCoordinateBound (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (ell : ℝ) : Prop :=
  ∀ (S : Finset (Fin n)) (_hcard : S.card < n)
    (hp : 0 < G.selectedSuccess strategy S),
    ∃ j, j ∉ S ∧
      (((G.repetition n).questions.condition (G.selectedWins strategy S) hp).probability
        (G.coordinateWin strategy j)) ≤
        G.value + 15 * Real.sqrt
          (((S.card : ℝ) * ell + logTwo (1 / G.selectedSuccess strategy S)) /
            ((n : ℝ) - S.card))

theorem repetition_success_le_of_conditionalCoordinateBound
    (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    {v ell : ℝ} (hvalue : G.value ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell)
    (hcoordinate : ConditionalCoordinateBound G n strategy ell) :
    (G.repetition n).success strategy ≤
      (1 - (1 - v)^3 / 6000)^((n : ℝ) / ell) := by
  have hpositive : ∀ S : Finset (Fin n), S.card < n →
      0 < G.selectedSuccess strategy S →
      ∃ j, j ∉ S ∧ SetStep (G.selectedSuccess strategy) v ell S j := by
    intro S hcard hp
    obtain ⟨j, hj, hbound⟩ := hcoordinate S hcard hp
    refine ⟨j, hj, ?_⟩
    change G.selectedSuccess strategy (insert j S) ≤ _
    rw [G.selectedSuccess_insert strategy S j hp]
    exact mul_le_mul_of_nonneg_left
      (hbound.trans (add_le_add hvalue (le_refl _))) (le_of_lt hp)
  obtain ⟨p, hp0, hpnonneg, hpmono, hrec, hpn⟩ :=
    exists_scalar_sequence (G.selectedSuccess strategy) v ell
      (G.selectedSuccess_empty strategy) (G.selectedSuccess_nonnegative strategy)
      (G.selectedSuccess_antitone strategy) hpositive
  have hbound := scalar_bound_6000 p n
    (G.value_nonnegative.trans hvalue) hv1 hell hp0 hpnonneg hpmono hrec
  rw [hpn, G.selectedSuccess_univ strategy] at hbound
  exact hbound

end DFVSGames.Foundations.Repetition.SelectionSequence

namespace DFVSGames.Foundations.Repetition
open scoped BigOperators
open Games
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selected_coordinate_probability_le_value_add_error
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability
      (G.coordinateWin strategy j.1) ≤
        G.value + selectedEmbeddingError G strategy selected positive j := by
  classical
  let : Nonempty (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
    finiteDistribution_nonempty (selectedProfileFallback G strategy selected positive j)
  have h := coordinate_probability_le_value_of_local_completion G j.1 strategy
    (selectedSamplingTarget G strategy selected positive j)
    (selectedLeftProfile G strategy selected positive j)
    (selectedRightProfile G strategy selected positive j)
    (selectedFullLeftCompletion G strategy selected j)
    (selectedFullRightCompletion G strategy selected j)
    (selectedFullLeftCompletion_support G strategy selected j)
    (selectedFullRightCompletion_support G strategy selected j)
    (Classical.choice inferInstance)
  have htarget : (selectedSamplingTarget G strategy selected positive j).mixture
      (fun z => (selectedFullLeftCompletion G strategy selected j (z.1.1,z.2)).product
        (selectedFullRightCompletion G strategy selected j (z.1.2,z.2))) =
      (G.repetition n).questions.condition (G.selectedWins strategy selected) positive :=
    selectedFullCompletionMixture_eq_conditionedQuestions G strategy selected positive j
  rw [htarget, selectedSamplingTarget_left_error, selectedSamplingTarget_right_error] at h
  exact h

theorem holenstein_conditionalCoordinateBound
    (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (ell : ℝ)
    (halphabet : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    SelectionSequence.ConditionalCoordinateBound G n strategy ell := by
  intro selected hcard positive
  obtain ⟨j,hj⟩ := exists_coordinate_le_information_budget G strategy selected positive ell
    halphabet hcard (selectedEmbeddingError G strategy selected positive)
    (selectedEmbeddingError_sum_le_fifteen G strategy selected positive)
  exact ⟨j.1,j.property,
    (selected_coordinate_probability_le_value_add_error G strategy selected positive j).trans
      (add_le_add le_rfl hj)⟩

theorem holenstein_repetition_success
    (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    {v ell : ℝ} (hvalue : G.value ≤ v) (hv : v < 1) (hell : 1 ≤ ell)
    (halphabet : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    (G.repetition n).success strategy ≤
      (1 - (1 - v)^3 / 6000)^((n : ℝ) / ell) :=
  SelectionSequence.repetition_success_le_of_conditionalCoordinateBound G n strategy
    hvalue hv hell (holenstein_conditionalCoordinateBound G n strategy ell halphabet)

theorem holenstein_repetition_value
    (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    {v ell : ℝ} (hvalue : G.value ≤ v) (hv : v < 1) (hell : 1 ≤ ell)
    (halphabet : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    (G.repetition n).value ≤
      (1 - (1 - v)^3 / 6000)^((n : ℝ) / ell) := by
  apply ((G.repetition n).value_le_iff _).2
  intro strategy
  exact holenstein_repetition_success G n strategy hvalue hv hell halphabet

end
end DFVSGames.Foundations.Repetition

end OAI
