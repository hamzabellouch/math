import OAI.Combinatorics.Ryser.Probability.Product

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.FiniteLaw

theorem map_map {Ω Γ Λ : Type*} [Fintype Ω] [Fintype Γ] [Fintype Λ]
    (mu : FiniteLaw Ω) (f : Ω → Γ) (g : Γ → Λ) :
    (mu.map f).map g = mu.map (g ∘ f) := by
  apply ext_weight
  funext z
  simp only [map_weight_eq_prob, prob_map, Function.comp_apply]

theorem map_pi {I : Type*} [Fintype I] [DecidableEq I]
    {A B : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (mu : ∀ i, FiniteLaw (A i)) (f : ∀ i, A i → B i) :
    (pi mu).map (fun a i => f i (a i)) = pi (fun i => (mu i).map (f i)) := by
  apply ext_weight
  funext b
  rw [map_weight_eq_prob]
  calc
    (pi mu).prob (fun a => (fun i => f i (a i)) = b) =
        (pi mu).prob (fun a => ∀ i, f i (a i) = b i) := by
      congr 1
      funext a
      exact propext ⟨fun h i => congrFun h i, fun h => funext h⟩
    _ = ∏ i, (mu i).prob (fun a => f i a = b i) :=
      prob_pi mu (fun i a => f i a = b i)
    _ = (pi (fun i => (mu i).map (f i))).weight b := by
      simp only [pi_weight, map_weight_eq_prob]

end RyserCoveringCounterexample.FiniteLaw

end

end OAI
