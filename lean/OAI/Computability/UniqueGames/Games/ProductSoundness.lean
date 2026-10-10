import OAI.Computability.UniqueGames.Games.ProductLemmas
import OAI.Computability.UniqueGames.Repetition.AnalyticCheegerLemmas
import OAI.Computability.UniqueGames.Repetition.TensorAlgebraLemmas

namespace OAI

section

/-!
The final graph product inherits the alphabet-independent repetition estimate
through its proved uniform occurrence law and arbitrary-local-strategy bridge.
The only input soundness premise is the base graph's actual finite maximum.
-/

namespace UniqueGamesTheorem.Explicit.BipartiteGame


open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {L R E A : Type*}
  [Fintype L] [Fintype R] [Fintype E] [Fintype A]
  [Nonempty E] [Nonempty A]

theorem product_soundness_rate (G : BipartiteGame L R E A) (t : ℕ)
    (hvalue : G.toGame.value ≤ 1 - (1 : ℝ) / 800) :
    (G.product t).toGame.value ≤ (1 - (1 : ℝ) / 10240000) ^ t := by
  rw [product_value_eq_repetition]
  exact UniqueGamesTheorem.Repetition.final_repetition_value
    G.toGame G.toGame_isProjection t hvalue

theorem product_soundness (G : BipartiteGame L R E A) (t : ℕ) {δ : ℝ}
    (hcount : (1 - (1 : ℝ) / 10240000) ^ t ≤ δ)
    (hvalue : G.toGame.value ≤ 1 - (1 : ℝ) / 800) :
    (G.product t).toGame.value ≤ δ :=
  (G.product_soundness_rate t hvalue).trans hcount

theorem product_explicit_soundness [DecidableEq A]
    (G : BipartiteGame L R E A) (t : ℕ) {δ : ℝ}
    (hcount : (1 - (1 : ℝ) / 10240000) ^ t ≤ δ)
    (hvalue : G.value ≤ 1 - (1 : ℝ) / 800) :
    (G.product t).value ≤ δ := by
  classical
  rw [← toGame_value]
  exact G.product_soundness t hcount (by simpa only [toGame_value] using hvalue)

end

noncomputable section

variable {L R E : Type*} [Fintype L] [Fintype R] [Fintype E] [Nonempty E]

theorem binaryProduct_soundness_rate {ell : ℕ}
    (G : BipartiteGame L R E (Fin ell → ZMod 2)) (t : ℕ)
    (hvalue : G.toGame.value ≤ 1 - (1 : ℝ) / 800) :
    (G.binaryProduct t).toGame.value ≤ (1 - (1 : ℝ) / 10240000) ^ t := by
  rw [binaryProduct_value_eq_repetition]
  exact UniqueGamesTheorem.Repetition.final_repetition_value
    G.toGame G.toGame_isProjection t hvalue

theorem binaryProduct_soundness {ell : ℕ}
    (G : BipartiteGame L R E (Fin ell → ZMod 2)) (t : ℕ) {δ : ℝ}
    (hcount : (1 - (1 : ℝ) / 10240000) ^ t ≤ δ)
    (hvalue : G.toGame.value ≤ 1 - (1 : ℝ) / 800) :
    (G.binaryProduct t).toGame.value ≤ δ :=
  (G.binaryProduct_soundness_rate t hvalue).trans hcount

theorem binaryProduct_explicit_soundness {ell : ℕ}
    (G : BipartiteGame L R E (Fin ell → ZMod 2)) (t : ℕ) {δ : ℝ}
    (hcount : (1 - (1 : ℝ) / 10240000) ^ t ≤ δ)
    (hvalue : G.value ≤ 1 - (1 : ℝ) / 800) :
    (G.binaryProduct t).value ≤ δ := by
  rw [← toGame_value]
  exact G.binaryProduct_soundness t hcount (by simpa only [toGame_value] using hvalue)

end

end UniqueGamesTheorem.Explicit.BipartiteGame

namespace UniqueGamesTheorem.Explicit.ProductPaddedOutput

open UniqueGamesTheorem.Foundations
open Target
open MachineOutputContract

noncomputable section

variable {q : ℕ} [Nonempty (Fin q)]

/-- Soundness for the actual globally numbered, fully tabulated output. -/
theorem output_soundness_rate (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t)
    (hvalue : Integration.InstanceValue.value H ≤ 1 - (1 : ℝ) / 800) :
    Integration.InstanceValue.value (output H presentation t ht) ≤
      (1 - (1 : ℝ) / 10240000) ^ t := by
  let : Nonempty (Fin H.constraints.length) := ⟨⟨0, H.constraintCount_positive⟩⟩
  rw [output_value_eq_repetition]
  apply UniqueGamesTheorem.Repetition.final_repetition_value
    presentation.toBipartiteGame.toGame presentation.toBipartiteGame.toGame_isProjection
  simpa only [BipartiteGame.toGame_value, presentation.toBipartiteGame_value] using hvalue

theorem output_soundness (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t) {δ : ℝ}
    (hcount : (1 - (1 : ℝ) / 10240000) ^ t ≤ δ)
    (hvalue : Integration.InstanceValue.value H ≤ 1 - (1 : ℝ) / 800) :
    Integration.InstanceValue.value (output H presentation t ht) ≤ δ :=
  (output_soundness_rate H presentation t ht hvalue).trans hcount

end
end UniqueGamesTheorem.Explicit.ProductPaddedOutput

end

end OAI
