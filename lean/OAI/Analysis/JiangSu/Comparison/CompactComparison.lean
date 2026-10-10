import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks

namespace OAI

section

namespace Pureness
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem uniform_index_of_increasing_open_cover (U : ℕ → Set T)
    (hopen : ∀ k, IsOpen (U k)) (hmono : Monotone U)
    (hcover : ∀ τ, ∃ k, τ ∈ U k) : ∃ k, ∀ τ, τ ∈ U k := by
  obtain ⟨k, hk⟩ := isCompact_univ.elim_directed_cover U hopen
    (fun τ _ => Set.mem_iUnion.mpr (hcover τ)) hmono.directed_le
  exact ⟨k, fun τ => hk (Set.mem_univ τ)⟩

theorem uniform_strict_index {R : Type*} [CompleteLinearOrder R]
    (F : T → R) (g : ℕ → T → R)
    (hopen : ∀ k, IsOpen {τ | F τ < g k τ})
    (hmono : ∀ τ, Monotone (fun k => g k τ))
    (hgap : ∀ τ, F τ < ⨆ k, g k τ) :
    ∃ k, ∀ τ, F τ < g k τ := by
  apply uniform_index_of_increasing_open_cover (fun k => {τ | F τ < g k τ}) hopen
  · intro i j hij τ hτ
    exact lt_of_lt_of_le hτ (hmono τ hij)
  · intro τ
    exact lt_iSup_iff.mp (hgap τ)

end Pureness
end

end OAI
