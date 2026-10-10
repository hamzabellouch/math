import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.SeedChainCounting

namespace OAI

/-!
# Counting indexed captured seed chains

Injective levels reduce a finite indexed family to a chain of natural-number levels.
Bounded seed offsets and the marked gaps then control the size of the original family.
-/

namespace RieszRectifiability

theorem indexed_captured_seed_chain_count {ι : Type*} (s : Finset ι) (O : Finset ℕ)
    (level seed : ι → ℕ) (I : ℕ) (hinj : Set.InjOn level s)
    (hseed : ∀ i ∈ s, level i ≤ seed i ∧ seed i ≤ level i + I)
    (hgap : ∀ i ∈ s, ∀ j ∈ s, seed i < level j →
      ∃ t ∈ O, seed i ≤ t ∧ t < level j) :
    s.card ≤ (I + 1) * (1 + O.card) := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨i₀, hi₀⟩ := hs
    let : Nonempty {i // i ∈ s} := ⟨⟨i₀, hi₀⟩⟩
    let f : {i // i ∈ s} → ℕ := fun i => level i.val
    have hf : Function.Injective f := by
      intro i j hij
      exact Subtype.ext (hinj i.property j.property hij)
    let g : ℕ → {i // i ∈ s} := Function.invFun f
    have hleft (i : ι) (hi : i ∈ s) : g (level i) = ⟨i, hi⟩ :=
      Function.leftInverse_invFun hf ⟨i, hi⟩
    have hb := captured_seed_chain_count (s.image level) O (fun l => seed (g l).val) I
      (by
        intro l hl
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
        simpa only [hleft i hi] using! hseed i hi)
      (by
        intro l hl m hm hlt
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
        simp only [hleft i hi] at hlt ⊢
        exact hgap i hi j hj hlt)
    rw [Finset.card_image_iff.mpr hinj] at hb
    exact hb
  · have heq : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [heq, Finset.card_empty, Nat.zero_le]

end RieszRectifiability

end OAI
