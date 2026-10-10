import Mathlib.Data.Finset.Insert
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace OAI

namespace Yau.Analysis

theorem finite_subsequence_selection {I : Type*} (P : Finset I)
    (R : I → (ℕ → ℕ) → Prop)
    (hex : ∀ i nu, StrictMono nu → ∃ mu : ℕ → ℕ, StrictMono mu ∧ R i (nu ∘ mu))
    (hsub : ∀ i nu mu, R i nu → StrictMono mu → R i (nu ∘ mu)) :
    ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∀ i ∈ P, R i nu := by
  classical
  induction P using Finset.induction_on with
  | empty => exact ⟨id,strictMono_id,by simp⟩
  | @insert i P hi ih =>
    obtain ⟨nu,hnu,hR⟩ := ih
    obtain ⟨mu,hmu,hm⟩ := hex i nu hnu
    refine ⟨nu ∘ mu,hnu.comp hmu,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hm
    · exact hsub j nu mu (hR j hj) hmu

end Yau.Analysis

end OAI
