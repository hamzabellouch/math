import Mathlib
import OAI.Computability.VertexCover.Games.Value
import OAI.Computability.VertexCover.Games.TotalVariation
import OAI.Computability.VertexCover.Games.Mixture

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                
section

namespace UniqueGames.Foundations.Games.Game

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
end UniqueGames.Foundations.Games.Game

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
