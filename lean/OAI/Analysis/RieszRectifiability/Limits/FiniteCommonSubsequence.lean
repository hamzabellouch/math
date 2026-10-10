import Mathlib

namespace OAI

namespace RieszRectifiability

open Function

theorem exists_finite_common_subsequence {ι : Type*} [Fintype ι]
    (P : ι → (ℕ → ℕ) → Prop)
    (hextract : ∀ i ρ, StrictMono ρ → ∃ σ : ℕ → ℕ, StrictMono σ ∧ P i (ρ ∘ σ))
    (hstable : ∀ i ρ σ, P i ρ → StrictMono σ → P i (ρ ∘ σ)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∀ i, P i ρ := by
  classical
  have hfinite (s : Finset ι) : ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∀ i ∈ s, P i ρ := by
    induction s using Finset.induction_on with
    | empty => exact ⟨id, strictMono_id, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨ρ, hρ, hP⟩ := ih
      obtain ⟨σ, hσ, hiP⟩ := hextract i ρ hρ
      refine ⟨ρ ∘ σ, hρ.comp hσ, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hiP
      · exact hstable j ρ σ (hP j hj) hσ
  obtain ⟨ρ, hρ, hP⟩ := hfinite Finset.univ
  exact ⟨ρ, hρ, fun i => hP i (Finset.mem_univ i)⟩

end RieszRectifiability

end OAI
