import OAI.GroupTheory.PolycyclicRecognition.Algebra.DirectedLowerCentral

namespace OAI

/-! # Every lower-central element occurs at one stage of an exhaustion -/

namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem lowerCentral_element_in_exhaustion (S : ℕ → Subgroup G) (hS : Monotone S)
    (hcover : ∀ g, ∃ n, g ∈ S n) (k : ℕ) (g : G)
    (hg : g ∈ (⊤ : Subgroup G).lowerCentralSeries k) :
    ∃ n, g ∈ (S n).lowerCentralSeries k := by
  have hne : (Set.range S).Nonempty := ⟨S 0, ⟨0, rfl⟩⟩
  have hdir : DirectedOn (· ≤ ·) (Set.range S) := by
    rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩
    exact ⟨S (max n m), ⟨max n m, rfl⟩, hS (le_max_left _ _), hS (le_max_right _ _)⟩
  have hsup : sSup (Set.range S) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨n, hn⟩ := hcover x
    exact (show S n ≤ sSup (Set.range S) from le_sSup ⟨n, rfl⟩) hn
  rw [← hsup] at hg
  obtain ⟨H, ⟨n, rfl⟩, hn⟩ := sSup_lowerCentralSeries_le_directedLowerCentral
    (Set.range S) hne hdir k hg
  exact ⟨n, hn⟩

end PolycyclicRecognition

end OAI
