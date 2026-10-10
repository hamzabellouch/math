import Mathlib
import OAI.Combinatorics.IndependentSets.Repetition.DistributionIdentities

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Repetition.CompletedSampling
open scoped BigOperators
open Games

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

end IndependentSetsGames.Foundations.Repetition.CompletedSampling

namespace IndependentSetsGames.Foundations.Games.Game

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

end IndependentSetsGames.Foundations.Games.Game

end

end OAI
