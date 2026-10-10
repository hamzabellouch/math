import Mathlib
import OAI.Computability.VertexCover.Games.Basic

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

namespace UniqueGames.Foundations.Games

open scoped BigOperators

noncomputable section

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]

def value (G : Game Q₁ Q₂ A₁ A₂) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty G.success

theorem success_le_value (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) : G.success strategy ≤ G.value := by
  classical
  exact Finset.le_sup' G.success (Finset.mem_univ strategy)

theorem value_le_iff (G : Game Q₁ Q₂ A₁ A₂) (bound : ℝ) :
    G.value ≤ bound ↔ ∀ strategy : Strategy Q₁ Q₂ A₁ A₂, G.success strategy ≤ bound := by
  classical
  simp [value, Finset.sup'_le_iff]

theorem exists_optimal_strategy (G : Game Q₁ Q₂ A₁ A₂) :
    ∃ strategy : Strategy Q₁ Q₂ A₁ A₂, G.success strategy = G.value := by
  classical
  obtain ⟨strategy, _, h⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Strategy Q₁ Q₂ A₁ A₂))) Finset.univ_nonempty G.success
  exact ⟨strategy, h.symm⟩

theorem value_nonnegative (G : Game Q₁ Q₂ A₁ A₂) : 0 ≤ G.value := by
  obtain ⟨strategy, h⟩ := G.exists_optimal_strategy
  rw [← h]
  exact G.success_nonnegative strategy

theorem value_le_one (G : Game Q₁ Q₂ A₁ A₂) : G.value ≤ 1 :=
  (G.value_le_iff 1).2 G.success_le_one

theorem randomized_success_le_value (G : Game Q₁ Q₂ A₁ A₂)
    {Seed : Type*} [Fintype Seed] (seedLaw : FiniteDistribution Seed)
    (strategies : Seed → Strategy Q₁ Q₂ A₁ A₂) :
    seedLaw.expectation (fun seed => G.success (strategies seed)) ≤ G.value := by
  unfold FiniteDistribution.expectation
  calc
    _ ≤ ∑ seed, seedLaw.weight seed * G.value := by
      apply Finset.sum_le_sum
      intro seed _
      exact mul_le_mul_of_nonneg_left (G.success_le_value _) (seedLaw.nonnegative seed)
    _ = G.value := by rw [← Finset.sum_mul, seedLaw.normalized, one_mul]

omit [Nonempty A₁] [Nonempty A₂] in
theorem success_repetition_zero (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin 0 → Q₁) (Fin 0 → Q₂) (Fin 0 → A₁) (Fin 0 → A₂)) :
    (G.repetition 0).success strategy = 1 := by
  have h : (G.repetition 0).wins strategy = fun _ => true := by
    funext questions
    simp [wins, repetition]
  unfold success
  rw [h, FiniteDistribution.probability_true]

@[simp] theorem value_repetition_zero (G : Game Q₁ Q₂ A₁ A₂) :
    (G.repetition 0).value = 1 := by
  obtain ⟨strategy, h⟩ := (G.repetition 0).exists_optimal_strategy
  rw [← h]
  exact G.success_repetition_zero strategy

theorem pow_value_le_repetition_value (G : Game Q₁ Q₂ A₁ A₂) (n : Nat) :
    G.value ^ n ≤ (G.repetition n).value := by
  obtain ⟨strategy, h⟩ := G.exists_optimal_strategy
  rw [← h, ← G.success_repeatStrategy strategy n]
  exact (G.repetition n).success_le_value (repeatStrategy strategy n)

theorem value_le_of_localSimulation {R₁ R₂ B₁ B₂ : Type*}
    [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂]
    [Nonempty B₁] [Nonempty B₂]
    (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂)
    (questionMap₁ : Q₁ → R₁) (questionMap₂ : Q₂ → R₂)
    (answerMap₁ : Q₁ → B₁ → A₁) (answerMap₂ : Q₂ → B₂ → A₂)
    (questionLaw : H.questions =
      G.questions.pushforward (fun q => (questionMap₁ q.1, questionMap₂ q.2)))
    (acceptance : ∀ x y a b,
      H.accepts (questionMap₁ x) (questionMap₂ y) a b = true →
      G.accepts x y (answerMap₁ x a) (answerMap₂ y b) = true) :
    H.value ≤ G.value := by
  apply (H.value_le_iff _).2
  intro strategy
  exact (G.success_le_of_localSimulation H questionMap₁ questionMap₂
    answerMap₁ answerMap₂ questionLaw acceptance strategy).trans (G.success_le_value _)

end Game

end

end UniqueGames.Foundations.Games

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
